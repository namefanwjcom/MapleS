# MapleS
The formal syntax and semantics of a core subset of MapleIR, based on [CompCert, version 3.7](http://compcert.inria.fr/).
MapleIR is the intermediate language of the openark compiler, see [here](https://gitee.com/openarkcompiler-incubator/mapleall/blob/master/doc/maple_ir_spec.md) for more information on MapleIR.

## Overview
The following files are written by me.

[Mapletypes.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/Mapletypes.v): the definition and preprocessing of types in MapleIR.

[MapleOp.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/MapleOp.v): the semantics of most arithmetic expressions and type conversion expressions.

[Maple.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/Maple.v): the core syntax and small-step operational semantics of MapleIR.

[MapleExec.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/MapleExec.v): the excutable small-step operational semantics of MapleIR and its correctness proof with respect to the relational semantics defined in [Maple.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/Maple.v).

[MapleBigstep.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/MapleBigstep.v): the big-step operational semantics of MapleIR.

[MapleDenotation.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/MapleDenotation.v): the denotational semantics of MapleIR.

[ITree.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/ITree.v): the modified version of InterationTrees, which is used in [MapleDenotation.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/MapleDenotation.v).

[TopoSort.v](https://github.com/namefanwjcom/MapleS/blob/master/lib/TopoSort.v): the implementation of the topological-sorting algorithm without any correctness proof, which is used in the preprocessing of types in [Mapletypes.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/Mapletypes.v).

## License
To be completed.

## Copyright
To be completed.

## Contact
If you have any question, please contact namefanwjcom@outlook.com.
