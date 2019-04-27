# Transformation of ML2 to Alloy

This project includes a transformation of models in the ML2 language [1] to Alloy. The transformation is written in Xtend and is incorporated in the ML2 Eclipse Editor see https://github.com/nemo-ufes/ML2-Editor (replacing ML2Generator.xtend).

The transformation is meant to support the validation and verification of ML2 models using the Alloy Analyzer. It reuses the [formal specification of MLT* in Alloy](https://github.com/nemo-ufes/mlt-ontology) [2].

There is also an example of transformation:

* [taxonomy.ml2](taxonomy-example/taxonomy.ml2) - an original ML2 model in the domain of biological taxonomy;
* [taxonomy.als](taxonomy-example/taxonomy.als) - the corresponding Alloy specification.

A [formalization of the representation strategy in TPTP syntax](tptp-formalization/preserving-semantics-multi-level.p) is also available. It was used to prove theorems in a forthcoming publication on the presentation of multi-level semantics in two-level techniques.

For further information see:
1. Fonseca, C.M., Almeida, J.P.A., Guizzardi, G., Carvalho, V.A.: Multi-level Conceptual Modeling: From a Formal Theory to a well-founded Language. In: 37th International Conference on Conceptual Modeling (ER 2018), LNCS, Springer, 2018, pp. 409–423. https://doi.org/10.1007/978-3-030-00847-5_29
2. Almeida, J. P. A., Fonseca, C. M., Carvalho, V. A., A Comprehensive Formal Theory for Multi-level Conceptual Modeling. In: 36th International Conference on Conceptual Modeling (ER 2017), LNCS, Springer, 2017. https://doi.org/10.1007/978-3-319-69904-2_2

If want to know more about ML2 and Multi-Level Theory (MLT), please visit our group's [webpage](https://nemo.inf.ufes.br/projects/mlt/).

Authors:
* Fernando Amaral Musso;
* João Paulo A. Almeida;


