#lang forge

sig Idx {}
one sig I1, I2, I3 extends Idx {}
-- add more later

sig Board {
     cages: set Cage
}

sig Solution {
     board: one Board
     values: set Idx->Idx->Int -- row -> col -> number
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

pred isWellFormedSolution[Solution] -- assert all cells have a value in [1, n]
pred isSolvedSolution[Solution] -- assert all cells are satisfied
pred isWellFormedBoard[Board] -- assert all cages are valid, all cells are in exactly one cage
pred isWellFormedCage[Cage] -- assert all cells are adjacent; if sub or div, max 2 cells
pred isSolvedCage[Cage, Solution] -- assert evaluateCage[Cage, Solution] == result

fun evaluateCage[Cage, Solution] -> Int
