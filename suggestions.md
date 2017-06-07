# Suggestions

  - Equality in Coq

    For the first meeting we said that one could prove "associativity
    of append for vectors (i.e. lists of a certain length)" as a
    warm-up exercise. This is, however, much more difficult than the
    analogous theorem for lists because we get different types on the
    two sides of the equality. (Daniel managed to prove this using JMeq.)

    - http://adam.chlipala.net/cpdt/html/Equality.html
    - http://sf.snu.ac.kr/gil.hur/publications/heq.pdf
    - http://web.mit.edu/jgross/Public/2014-splash/equality/exercises.v

  - Proof by reflection and SSReflect

    - http://adam.chlipala.net/cpdt/cpdt.pdf#chapter.15
    - https://team.inria.fr/marelle/en/advanced-coq-winter-school-2016/ -- difficult to follow (according to Andreas)
    - https://github.com/math-comp/wiki/wiki/tutorial-itp2016
    - https://math-comp.github.io/mcb/
    - http://ilyasergey.net/pnp/

  - Writing tactics (proof automation)

    - Ltac (“not the most beautiful part of Coq”)

      http://adam.chlipala.net/cpdt/cpdt.pdf#chapter.14

      [Nisse](http://www.cse.chalmers.se/~nad/) recommended going deep into Ltac with Chlipala's book if we have the time.
      (Which we should, getting the proof of normalization of the simply-typed
      lambda calculus using logical relations should be easy).

    - [Mtac](http://plv.mpi-sws.org/mtac/) (typed tactic programming)

  - Generic programming

    http://adam.chlipala.net/cpdt/cpdt.pdf#chapter.11

  - Proofs about arithmetic

    Classical results:

    - Irrationality of the square root of two ([Cocorico!](https://coq.inria.fr/cocorico/SquareRootTwo)).
    - Infinitude of primes ([MCB](https://math-comp.github.io/mcb/book.pdf#page=112) [proof](https://math-comp.github.io/mcb/ch4.html)).

  - Program extraction

    - Covered in one chapter in SF, but more info in Extraction in VFA
    - Examples with simple programs?
    - Efficiency of extracted programs?
    - [Coq.io](http://coq.io)
    - Any formal guarantees on extracted programs or are they simply pretty-printed?

  - Large proof projects

    - CompCert
    - [Formalized mathematics](https://coq.inria.fr/cocorico/List%20of%20Coq%20Math%20Projects) (four color theorem often mentioned)

  - Abus de notation: Type classes/Canonical structures/Coercions/Unification hints/Mooooooonads

    - TODO: Good documentation for this? Exercises?

  - Matthieu Sozeau's [Program](https://coq.inria.fr/refman/Reference-Manual027.html) tactics and [Equations](https://www.irif.fr/~sozeau/research/coq/equations.en.html) plugin

    - TODO: Good documentation for this? Exercises?

  - See also the [links/books/references](README.md#reference-material) in the README
