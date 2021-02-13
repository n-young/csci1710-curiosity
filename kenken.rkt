#lang forge

-- ====================================================================
-- SIGNATURES
-- ====================================================================

sig Idx {
    next: lone Idx
    prev: lone Idx
}
one sig I1, I2, I3, I4 extends Idx {}

pred isWellFormedIdx {
    
}


sig Board {
    cages: set Cage
}

sig Solution {
    board: one Board
    values: set Idx->Idx->Int
}

sig Cage {
    operation: one Operation
    cells: set Idx->Idx
    result: Int
}

abstract sig Operation {}
one sig Addition extends Operation {}
one sig Subtraction extends Operation {}
one sig Multiplication extends Operation {}
one sig Division extends Operation {}

-- ====================================================================
-- PREDICATES
-- ====================================================================

pred isWellFormedSolution[Solution] -- assert all cells have a value in [1, n]
pred isSolvedSolution[Solution] -- assert all cells are satisfied
pred isWellFormedBoard[Board] -- assert all cages are valid, all cells are in exactly one cage
pred isWellFormedCage[Cage] { -- assert all cells are adjacent; if sub or div, max 2 cells
   all c: Cell |
       c in Cage.cells |
           some a:Cell |
               
}
pred isSolvedCage[Cage, Solution] -- assert evaluateCage[Cage, Solution] == result

-- ====================================================================
-- TESTS
-- ====================================================================

pred isWell

fun evaluateCage[Cage, Solution] -> Int
