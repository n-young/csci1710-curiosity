#lang forge

-- ====================================================================
-- SIGNATURES
-- ====================================================================

abstract sig Idx {
    neighbor: lone Idx
}
one sig I1, I2, I3, I4 extends Idx {}

pred isWellFormedIdx {
    neighbor = I1->I2 + I2->I3 + I3->I4
}


sig Board {
    cages: set Cage
}

sig Solution {
    board: one Board,
    values: set Idx->Idx->Int
}

sig Cage {
    operation: one Operation,
    cells: set Idx->Idx,
    result: one Int
}

abstract sig Operation {}
one sig Addition extends Operation {}
one sig Subtraction extends Operation {}
one sig Multiplication extends Operation {}
one sig Division extends Operation {}

-- ====================================================================
-- PREDICATES
-- ====================================================================

pred isWellFormedSolution[soln: Solution] {
    -- assert all cells have a value in [1, n]
}

pred isSolvedSolution[soln: Solution] {
    -- assert all cells are satisfied
}

pred isWellFormedBoard[board: Board] {
    -- assert all cages are valid, all cells are in exactly one cage
}

pred isWellFormedCage[cage: Cage] {
    -- assert all cells are adjacent; if sub or div, max 2 cells
    some cage.cells
    all row: Idx | all col: Idx | row->col in cage.cells implies {
        some cage.cells & (row->(col.neighbor) + row->(neighbor.col) + (row.neighbor)->col + (neighbor.row)->col)
    }
    cage.operation in Subtraction + Division implies #(cage.cells) = 2
}

pred isSolvedCage[cage: Cage, soln: Solution] {
    -- assert evaluateCage[Cage, Solution] == result
}
-- ====================================================================
-- TESTS (isWellFormedCage)
-- ====================================================================

example StandardCage is {isWellFormedCage[Cage]} for {
    I1 = I10
    I2 = I20
    I3 = I30
    I4 = I40
    neighbor = I1->I2 + I2->I3 + I3->I4
    Cage = Cage0
    Multiplication = Multiplication0
    operation = Cage0->Multiplication0
    cells = Cage0->I10->I10 + Cage0->I20->I10
    result = Cage0->7
}

inst TestCage {
    I1 = I10
    I2 = I20
    I3 = I30
    I4 = I40
    neighbor = I1->I2 + I2->I3 + I3->I4
    Cage = Cage0
    Multiplication = Multiplication0
    operation = Cage0->Multiplication0
    cells = Cage0->I10->I10 + Cage0->I20->I10
    result = Cage0->7
}

run {
    isWellFormedIdx
    all c: Cage | isWellFormedCage[c]
} for exactly 1 Cage, 0 Solution, 0 Board
