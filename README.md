# MapleS
The formal syntax and semantics of MapleLight, a core subset of MapleIR, based on Coq, CompCert and InteractionTrees.
MapleIR is the intermediate language of the openark compiler, see [here](https://gitee.com/openarkcompiler-incubator/mapleall/blob/master/doc/maple_ir_spec.md) for more information about MapleIR.

### See:
- [Coq](https://coq.inria.fr/)
- [CompCert](http://compcert.inria.fr/)
- [InteractionTrees](https://github.com/DeepSpec/InteractionTrees)

## Overview
All files in the [Maple](https://github.com/namefanwjcom/MapleS/tree/master/Maple) directory are written by me.

```
├── [Maple](https://github.com/namefanwjcom/MapleS/tree/master/Maple)
│   ├── [coq](https://github.com/namefanwjcom/MapleS/tree/master/Maple/coq)
│   │   ├──[MapleAST.v](https://github.com/namefanwjcom/MapleS/blob/master/Maple/coq/MapleAST.v): the abstract syntax of MapleLight.
│   │   ├──
│   │   ├──
│   │   ├──[MapleLightTypes.v](https://github.com/namefanwjcom/MapleS/blob/master/Maple/coq/MapleLightTypes.v): the definition and preprocessing of types in MapleLight.
│   │   ├──[MapleLightOp.v](https://github.com/namefanwjcom/MapleS/blob/master/Maple/coq/MapleOp.v): the semantics of most arithmetic expressions and type conversion expressions.
│   │   ├──
│   │   ├── 
│   │   ├── **/*.css
│   ├── favicon.ico
│   ├── images
│   ├── index.html
│   ├── js
│   │   ├── **/*.js
│   └── partials/template
├── dist (or build)
├── node_modules
├── bower_components (if using bower)
├── test
├── Gruntfile.js/gulpfile.js
├── README.md
├── package.json
├── bower.json (if using bower)
└── .gitignore
```



[MapleOp.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/MapleOp.v): the semantics of most arithmetic expressions and type conversion expressions.

[Maple.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/Maple.v): the core syntax and small-step operational semantics of MapleIR.

[MapleExec.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/MapleExec.v): the excutable small-step operational semantics of MapleIR and its correctness proof with respect to the relational semantics defined in [Maple.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/Maple.v).

[MapleBigstep.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/MapleBigstep.v): the big-step operational semantics of MapleIR.

[MapleDenotation.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/MapleDenotation.v): the denotational semantics of MapleIR.

[ITree.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/ITree.v): the modified version of InterationTrees, which is used in [MapleDenotation.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/MapleDenotation.v).

[TopoSort.v](https://github.com/namefanwjcom/MapleS/blob/master/lib/TopoSort.v): the implementation of the topological-sorting algorithm without any correctness proof, which is used in the preprocessing of types in [Mapletypes.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/Mapletypes.v).

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
