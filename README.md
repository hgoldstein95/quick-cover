# QuickCover

Property-based testing uses randomly generated inputs to validate high-level
program  specifications. It can be shockingly effective at finding bugs, but it
often requires generating a very large set of inputs to do so.  This repository
applies ideas from combinatorial testing, a powerful and widely studied testing
methodology, to modify the distributions of random generators and find bugs
with fewer tests. The key concept is combinatorial coverage, which measures the
degree to which a given set of tests exercises every possible choice of values
for every small combination of inputs.

In its "classical" form, combinatorial coverage only applies to programs taking
inputs of a very constrained shape: essentially, a Cartesian product of finite
sets. We generalize combinatorial coverage to the richer world of algebraic
data types by formalizing a class of sparse test descriptions based on regular
tree expressions. This new definition of coverage inspires a novel
combinatorial thinning algorithm for improving the coverage ofrandom test
generators, requiring many fewer tests to catch bugs. We evaluate the new
method on two case studies, a typed evaluator for System F terms and a Haskell
compiler, showing significant improvements in both

*Note* This repository is a work in progress. QuickCover is not yet packaged as
a ready-to-use tool, although the theory behind it is sound.

## Important Files

The main implementation of the QuickCover algorithm can be found in
[SystemFExperiments.hs](src/SystemFExperiments.hs). We define and manipulate
our sparse test descriptions in [HT.hs](src/HT.hs).

[Main.hs](app/Main.hs) runs the System F experiment from the paper
evaluation---edit `experiments` at the bottom of
[SystemFExperiments.hs](src/SystemFExperiments.hs) to manipulate the experiment
parameters.

