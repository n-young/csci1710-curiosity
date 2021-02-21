# Curiosity Modelling - KenKen
Jed Fox and Nick Young

## What is KenKen?

We are modelling [KenKen](https://en.wikipedia.org/wiki/KenKen) (sometimes called KenDoku), a Japanese puzzle game similar to Sudoku, but with an arithmetic twist. The objective of KenKen is to fill an `n` by `n` grid of digits such that:

- Every column has distinct values between 1 and `n`, inclusive,
- Every row has distinct values between 1 and `n`, inclusive,
- The values in every cage either sum, subtract, multiply, or divide to a target value.

The first two rules are simple, the third requires explanation. A KenKen board is split into cages, which surround some number of squares and have an operation and a target value. A filled cage should have its values reach the target value using the specified operation. Usually, subtraction and division cages are limited to having exactly two cells, and any cage with one cell just has a fixed value and no operation. Not all variants of KenKen work this way, but ours does.


## Design Choices

Aside from the given constraints of standard KenKen, we added our own constraints to make the problem simpler to approach. We:

- Fixed the board size to 4, since 3 wasn't particularly interesting, and 5 had trouble running in reasonable time,
- Set the maximum cage size to 3, since ensuring that cages didn't split into islands was prohibitively difficult,
- Asserted that cages have distinct values, since sets disallow multiplicity, doing math over sets wasn't clean.

With enough time, we could probably remove these overconstraints, but adding them made the problem much more doable.


## Running KenKen

Our testing ensures wellformedness of cages, boards, and solutions, and ensures that evaluation (on cages and solutions that fit our overconstraints) works.

When running KenKen, we recommend running something like:

```alloy
run {
    isWellFormedIdx
    all s: Solution | isSolvedBoard[s]
} for exactly 6 Int, exactly 1 Solution, exactly 1 Board, exactly 7 Cage
```

The `isWellFormedIdx` predicate ensures that the `neighbors` relation is fixed properly. Otherwise, the rest of the predicate searches for a solved board. We found that running with anything other than `6 Int` breaks Forge or returns erroneous results. We also recommend running with `exactly 1 Solution, exactly 1 Board`. The number of cages is tweakable, but we found the most interesting boards with `exactly 7 Cage`.

The program takes a little while to run, but when done, use the visualizer in `vis.js` with `<div>` mode to see a board and its solution!


## Implementation Details

### Signatures

The `Idx` sig represents a row or column index on the board. It was simpler to work with defined sigs than Ints here.

The `Operation` sig is essentially an enum over operation types.

The `Cage` sig is a cage. Each cage has one `operation` and one `result`, and a set of `Idx->Idx` pairs that represent which squares the cage surrounds.

The `Board` sig is a board. Each board has a set of `cages`.

The `Solution` sig is a solution. Each solutoin has one `Board` that it solves for, as well as a set of `Idx->Idx->Int` values that specify what each cell should have as its value.

### Predicates

The `isWellFormedCage` predicate ensures that a cage has between 1 and 3 cells, that cells are connected, that if a cage has one cell that its operation is addition, and that if the cage operation is subtraction or division, it has two cells.

The `isWellFormedBoard` predicate ensures that a board has nonoverlapping cages that cover the entire board, and that each board is well formed.

The `isWellFormedSolution` predicate ensures that its board is well formed, that the solution values correspond to the board cells properly, that each row and column has distinct values between 1 and n, and that each cage has distinct values.

The `isSolvedCage` predicate ensures that a given cage is solved correctly - that is, depending on the operation, the values reach the target value. To do this, we had to use some weird branching and maths.

The `isSolvedBoard` predicate ensures that a given solution is well formed, and every cage is solved.
