# Mechanizations of Type Theories

This is a collection of mechanizations of type theories during [Jason
Hu](https://hustmphrrr.github.io/)'s PhD at McGill University. This library mechanizes
the normalization proofs of many type theories using different methods. A notable one
is untyped domain models as per [Abel](https://www.cse.chalmers.se/~abela/habil.pdf). 
Please read [README](README.html) for a list of available type theories. 

This library also demonstrates that, at least for mechanizations of normalization
proofs, Agda does not necessarily require more lines of code than proof assistants
with very powerful proof automation, e.g. Coq. For example, the whole normalization
proof with completeness and soundness theorems for [Martin-Löf type theory](MLTT.README.html) is around
8000 LoC. This is the smallest proof in size among all similar mechanizations in 2024, while
there is still room to further shorten the mechanization.

This library current works with Agda 2.7.0.1 and agda-stdlib 2.2.1. 

You are welcome to use it anywhere, for teaching or for your own research. Please also
feel free to contribute. 

## Related Projects and Papers

1. Jason Z. S. Hu and Brigitte Pientka. A Categorical Normalization Proof for the
   Modal Lambda-Calculus (**MFPS 22**)
   
   [See the code](Unbox.README.html)

1. Jason Z. S. Hu, Junyoung Jang and Brigitte Pientka. Normalization by Evaluation for Modal Dependent Type Theory (**JFP 23**)
   
   [See the code](Mint.README.html)

   Please also see [here](https://hustmphrrr.github.io/Kripke-style/). 

1. Jason Z. S. Hu and Brigitte Pientka. Layered Modal Type Theory: Where
   Meta-programming Meets Intensional Analysis (**ESOP 24**)

   [See the code](Layered.README.html); [also](CLayered.README.html)

Audience interested in this library might also find [another
project](https://github.com/Beluga-lang/McTT) that Jason Hu is involved in interesting
too.

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
git checkout release-2.6.4.3
cp stack-8.8.4.yaml stack.yaml # choose your favourite Haskell version
stack install # it is going to take a while
cp ~/.local/bin/agda ~/.local/bin/agda-2.6.4.3
cp ~/.local/bin/agda-mode ~/.local/bin/agda-mode-2.6.4.3
```

If Agda does not run, please check to make sure it is in your PATH.

## Foundation and Assumptions

This library is implemented in safe Agda without K as much as possible. For dependent
type theories, however, it is necessary to include the extension of
induction-recursion. Functional extensionality is sometimes used for dependent type
theories as well. These extensions are completely standard, as done in many other
works. 
