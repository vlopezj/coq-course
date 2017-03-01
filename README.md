# Coq @ Chalmers

Coq course at the Chalmers CSE department, in principle for PhD students.

*Disclaimer:*
- *This course is not guaranteed to take place. Times, contents and evaluation form are provisional and subject to change.*
- *This course is planned as a self-reading course. As such, each person is individually responsible for fulfiling the goals set by the examiner. No assistance is provided beyond what other participants are willing and able to give.*

## Dates

The course will take place during 2017 LP3.

- Kick-off meeting: Thu 2nd Feb, 3:15pm-5pm, room 6128. [Plan](plan.md), [Notes](notes/session01.md)
- Session 2: Thu 16th Feb, 3:15-5pm, room 6128. [Notes](/notes/session02.md)
- Session 3: Thu 2nd Mar, 3:15-5pm, room 6128. [Agenda](/notes/session03.md)

### Deliverables

Coq files with solutions to the exercises. Deliverables are uploaded to a separate, [**private repository**](https://github.com/dschoepe/coq-course-exercises).

## Prerequisites

Participants are expected to be familiar with a functional language
with a rich type system, such as Agda, Haskell or Scala. They
should also be able to use induction to prove properties about
the natural numbers, or any other inductively defined set.

## Course plan

See **[syllabus.md](syllabus.md)** and **[plan.md](plan.md)** for more details.

## Reference material

General reference material for the course.

### Books

From [Coq at nLab](https://ncatlab.org/nlab/show/Coq):

+ Benjamin Pierce’s [Software Foundations](http://www.cis.upenn.edu/~bcpierce/sf) (SF) is probably the most elementary introduction to Coq and functional progamming. The book is written in Coq so you can directly open the source files in CoqIDE and step through them to see what is going on and solve the exercises.

  This book should be good for people with a CS background (and some PL on top of that).

  SF uses Coq for the formalization of programming languages.

+ Adam Chlipala’s [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) (CPDT) explains more advanced Coq techniques.

  It relies heavily on tactics, which can be an impediment if one actually cares about the proof.

  CPDT uses Coq as a programming language with a rich type system.

+ [Mathematical Components](https://math-comp.github.io/mcb/book.pdf) by Assia Mahboubi, Enrico Tassi with contributions by Yves Bertot and Georges Gonthier:

  > This books targets two classes of public.  On one hand newcomers, even the
  > more mathematical inclined ones,  find a soft introduction to the programming
  > language of Coq, Gallina, and the *Ssreflect* proof language.  On the other hand
  > accustomed Coq users find a substantial account of the formalization style that
  > made the Mathematical Components library possible.

  Mathcomp focuses on practical math, more on the discrete algebra side
  (natural and polynomial arithmetic, finite dimensional linear algebra,
  finite group theory, representations, ... + some finite graph theory).

+ [Verified Functional Algorithms](https://www.cs.princeton.edu/~appel/vfa/) by Andrew W. Appel. "Volume 3 of the Software Foundations series".

Comparison between [SF, CPDT and Coq’Art](http://lambda.jstolarek.com/2016/06/coqart-cpdt-and-sf-a-review-of-books-on-coq-proof-assistant/).

### Tutorials

  - [Coq tutorial @ ITP 2015](https://coq.inria.fr/coq-itp-2015)
  - [Basic Coq tutorial by Yves Bertot](https://team.inria.fr/marelle/en/coq-winter-school-2016/)
  - [Advanced mathcomp tutorial (1 week)](https://team.inria.fr/marelle/en/advanced-coq-winter-school-2016/) -- contains non-trivial maths
  - [Short mathcomp tutorial @ ITP 2016](https://github.com/math-comp/wiki/wiki/tutorial-itp2016)
  - Coq is covered in some Oregon Programming Languages Summer School iterations, e.g. [Chlipala's sessions from 2015](https://www.cs.uoregon.edu/research/summerschool/summer15/curriculum.html) (video format)

### Fun links

  - [Haskell for Coq programmers](http://blog.ezyang.com/2014/03/haskell-for-coq-programmers/)

### Exercises

+ [Exercises written for Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/ex/):

  + [Snapshot of exercises](http://adam.chlipala.net/cpdt/ex/exercises.pdf) that were included in CPDT when I decided to stop maintaining exercises -- Adam Chlipala

  + [Homeworks from CIS 670 at Penn in Fall 2012](http://www.cis.upenn.edu/~bcpierce/courses/670Fall12/) -- Benjamin Pierce and students in the class

+ [Exercises from the 2012 International Spring School on FORMALIZATION OF MATHEMATICS](http://www-sop.inria.fr/manifestations/MapSpringSchool/program.html)

+ There are quite many exercises in Pierce's SF book.

+ [Modelling and verifying algorithms in Coq: an introduction](http://www.di.ens.fr/~zappa/teaching/coq/ecole11/), yet another introductory tutorial, has some exercises.

## Examination

Examiner: [Thierry Coquand](http://www.cse.chalmers.se/~coquand/)

Credits: 7.5, but the final decision about how many credits the course gives rests with each participant’s respective examiner.

Full participation is required. This entails attending the meetings, doing the exercises and presenting some of them.



## IRC channel

We set up an IRC channel for discussing the course:

    ##coq@chalmers on freenode

Note that there are *two hashes* in the channel name.

If you don't want to run your own server for running a client continuously, you
can use [riot's](http://riot.im) IRC bridge:

- Create a [riot](http://riot.im/) account
- Join the [channel](https://riot.im/app/#/room/#freenode_##coq@chalmers:matrix.org)

## Participants

+ Fabian Ruch
+ Andrea Vezzosi
+ Víctor López Juan
+ Herbert Lange
+ Daniel Schoepe
+ Irene Lobo Valbuena
+ YuTing Chen (jeff)
+ Andreas Lööw
+ Simon Robillard
+ Marco Vassena
+ Simon Huber

The course has started. If you still want to **take part**, you can *add your name to the list of participants* by [editing this file online][edit] and sending in a pull request. Be aware that you might have to work harder in the beginning in order to catch up.

If you have questions, issues or patches, and do not want to use a Github account, you can e-mail <project-coq-course@lopezjuan.com> instead.

[**Edit this file**][edit]

[edit]: https://github.com/vlopezj/coq-course/edit/master/README.md
