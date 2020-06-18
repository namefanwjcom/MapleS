# MapleS
The formal syntax and semantics of a core subset of MapleIR, based on [CompCert, version 3.7](http://compcert.inria.fr/).
MapleIR is the intermediate language of the openark compiler, see [here](https://gitee.com/openarkcompiler-incubator/mapleall/blob/master/doc/maple_ir_spec.md) for more information on MapleIR.

## Overview
The following files are written by me.

[Maple.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/Maple.v): the core syntax and semantics of MapleIR.

[Mapletypes.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/Mapletypes.v): the definition and preprocessing of types in MapleIR.

[MapleOp.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/MapleOp.v): the semantics of most arithmetic expressions and type conversion expressions.

[MapleExec.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/MapleExec.v): the excutable semantics of MapleIR and its correctness proof with respect to the semantics defined in [Maple.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/Maple.v).

[TopoSort.v](https://github.com/namefanwjcom/MapleS/blob/master/lib/TopoSort.v): the implementation of the topological-sorting algorithm without any correctness proof, which is used in the preprocessing of types in [Mapletypes.v](https://github.com/namefanwjcom/MapleS/blob/master/cfrontend/Mapletypes.v).

## License
To be completed.

## Copyright
To be completed.

## Contact
If you have any question, please contact namefanwjcom@outlook.com.