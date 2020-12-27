# MapleS
The formal syntax and semantics of MapleLight, a core subset of MapleIR, based on Coq, CompCert and InteractionTrees.

### See:
- [MapleIR](https://gitee.com/openarkcompiler-incubator/mapleall/blob/master/doc/maple_ir_spec.md): the intermediate language of the openark compiler
- [Coq](https://coq.inria.fr/)
- [CompCert](http://compcert.inria.fr/)
- [InteractionTrees](https://github.com/DeepSpec/InteractionTrees)

## Overview
All files in the [Maple](https://github.com/namefanwjcom/MapleS/tree/master/Maple) directory are written by me.

```
Maple
├── coq
│   ├── MapleAST.v: the abstract syntax of the subset of MapleIR corresponding to MapleLight
│   ├── MapleInter.v: the intermediate language from the MapleAST to MapleLight
│   ├── MapleLight.v: the syntax and small-step operational semantics of MapleIR
│   ├── MapleLightTypes.v: the definition and preprocessing of types in MapleLight
│   ├── MapleLightOp.v: the semantics of most arithmetic expressions and type conversion expressions in MapleLight
│   ├── MapleLightExec.v: the excutable small-step operational semantics of MapleLight and its correctness proof with respect to the relational semantics defined in MapleLight.v
│   ├── MapleLightDenotation.v: the denotational semantics of MapleLight based on InteractionTrees
│   └── TopoSort.v: the implementation of the topological-sorting algorithm without any correctness proof, which is used in the preprocessing of types in MapleLightTypes.v
├── extraction
│   └── Extraction.v: extracts the executable semantics in MapleLightDenotation.v into ocaml code
├── transformer
│   ├── lexer.mll: describes the regular expression of legal tokens in MapleAST, from which ocamllex generates a lexer
│   ├── parser.mly: describes the context free grammar of MapleAST, from which menhir generates a parser that parses real MapleIR programs(in the form of plain text) into MapleAST programs(in the form of ocaml code)
│   ├── MapleAST2MapleInter.ml: transforms MapleAST programs to MapleInter programs
│   ├── MapleInter2MapleLight.ml: transforms MapleInter programs to MapleLight programs
│   ├── PrintMapleAST.ml: prints the MapleAST programs as plain text for the ease of reading and testing
│   ├── PrintMapleInter.ml: prints the MapleInter programs as plain text for the ease of reading and testing
│   ├── PrintMapleLight.ml: prints the MapleLight programs as plain text for the ease of reading and testing
│   └── Exception.ml: defines two kinds of exceptions, i.e., CompilationError and Abort
├── driver
│   └── mapleinterp.ml: the top-level part of the interpreter which combines the transformer and the extracted semantics
├── doc
│   └── MapleLight.pdf: documentation on the syntax and small-step operational semantics of MapleLight
└── test: the directory containing testing files(xxx.mpl)
```

## Dependencies
- os: Ubuntu 18.04 x64
- coq: 8.11.1
- ocaml: 4.10.0
- External ocaml/coq libaries:
  * coq-itree: 3.2.0
  * menhir: 20200612

See [here](https://coq.inria.fr/opam-using.html) to learn how to install coq, ocaml and the external libaries if you are not familiar with coq.

## Compilation && Running
You can compile the project and run the generated interpreter on a `.mpl' file to test the semantics through the following instructions.

`make maple'
`cd Maple'
`./mapleinterp test/xxx.mpl'

## Contact
If you have any question, please contact namefanwjcom@outlook.com.
