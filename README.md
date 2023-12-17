# Welcome
Hello and welcome to our COMP 703 course project. We developed and implemented a theorem proving algorithm for constructive logic, abstract code extraction using the Curry-Howard correspondence, and built a code synthesizer for OCaml. For more specifics, please see the final project report in this repository.

# Usage
This project requires OCaml 5.1.0 or greater, although it has only been tested on 5.1.0. We build and run our project with Dune. Executing the [runMe.sh](https://github.com/TravisNP/COMP703/blob/main/COMP_PROVER/runMe.sh) file will run the [testing.ml](https://github.com/TravisNP/COMP703/blob/main/COMP_PROVER/bin/testing.ml) file. There are examples in this file which will help you learn how to create and extract functions for your own theorems.

First, to specify a theorem, you must know how to use the implication, conjunction, disjunction, and not operators. The not operator is !!, cunjunction **, disjunction @@, and implication &&. This may seem confusing at first as why would && stand for implication and not conjunction? The operator precedence and associativity [table](https://v2.ocaml.org/manual/expr.html) on the OCaml manual provides an explanation. As the constructive logic operators have precedence order and are right associative, our choice of operators becomes severely limited, and so we tried to make our choice as least confusing as possible. We could have used an external package to make the operators clear, however, we did wanted the setup to be as least complicated as possible and so we chose to have our project work with no external packages.

Second, if you have not read the paper you will need to know how our custom theorem type is defined. Singleton theorems, those with no operators, are defined with the constructor S and take in a single integer. To make this easier, we have included a shorthand for around the first half of the alphabet. That is, the letter a corresponds to S 0, b to S 1, etc. For example, the first theorem in testing.ml, a ** b && b ** a, is shorthand for (S 0) ** (S 1) && (S 1) ** (S 0).

Finally, we provide several userfriendly functions, although all are exposed to the user. First, the theorem_to_proof function takes in a theorem and gives a corresponding proof. If no proof exists or none is found, a proof with the rule of failure is returned. Theorem_to_proof also takes in an optional argument maxDepthBuildUp, which specifies the maximum amount of building up rules that can be used in a branch of the proof tree. For example, 
```
theorem_to_proof ~maxDepthBuildUp:10 a ** b && b ** a
```
tries to prove the first theorem in the testing.ml file with a max depth of 10. The default max depth is 100.

The second function needed is the proof_to_program function, which takes in a proof and returns the corresponding program.

The third function is program_to_ocaml_string, which takes in a program returns a string of runnable OCaml code.

These can be ran all at once on a single theorem using the [test_theorem](https://github.com/TravisNP/COMP703/blob/5151ff43e3d098f7c4233bc0007f31167299578c/COMP_PROVER/lib/Prover.ml#L631-L645) function. This function also takes in the optional argument of maxDepthBuildUp. 

In terms of to_string and printing, we provide the following functions: theorem_to_string, print_theorem, proof_to_string, print_proof, proof_to_oneline_string, print_proof_oneline, program_to_string, and print_program functions. The oneline versions give the proof as string form in one compact line, but it is less readable for larger functions than the multi-line version.

To see the output of the current contents of the testing.ml file, you can look at the [output.txt](https://github.com/TravisNP/COMP703/blob/main/COMP_PROVER/output.txt) file, or run it yourself!
