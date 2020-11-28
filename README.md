# L-lang Parser

A parser for a toy strict untyped λ-calculus language called L-lang.

## Get Started

### L Language

You may view the syntax of L-lang in [l.pest](src/l.pest).

There's an example L-lang program called [run.l](run.l). 

### Export to Coq code

``` coq
$ l-lang-parser-rs export run.l
Definition my_evenb: tm :=
  (rec (abs "my_evenb"
    (abs "n"
      (mat (var "n") [
        ("S", ["x"],
          (mat (var "x") [
            ("S", ["x"],
              (app (var "my_evenb") (var "x")));
            ("O", [],
              (const "false"))
          ]));
        ("O", [],
          (const "true"))
      ])
    )
  )).

Definition main: tm :=
  (app my_evenb (app (const "S") (app (const "S") (app (const "S") (app (const "S") (const "O")))))).
```

### Run program

``` coq
$ l-lang-parser-rs export run.l
     = Some (const "true")
     : option tm
```

## License

This project is licensed under the [Apache License 2.0](LICENSE.md).
