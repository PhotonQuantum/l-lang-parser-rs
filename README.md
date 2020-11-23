# L-lang Parser

A parser for a toy strict untyped λ-calculus language called L-lang.

## Get Started

You may view the syntax of L-lang in [l.pest](src/l.pest).

There's an example L-lang program called [run.l](run.l). 
Beware that the semantics of this file is not guaranteed to be correct or meaningful. 

By compiling and running the parser, you will get the ast of [run.l](run.l).

The final goal of this parser is to generate coq code of a given L-lang program as HIR to make it possible for me to write L-lang programs directly instead of constructing its HIR by hand.

## License

This project is licensed under the [Apache License 2.0](LICENSE.md).