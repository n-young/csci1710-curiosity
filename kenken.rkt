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

pred isWellFormedCage[cage: Cage] {
    -- assert all cells are adjacent; if sub or div, max 2 cells
    some cage.cells
    all row: Idx | all col: Idx | row->col in cage.cells implies {
        some cage.cells & (row->(col.neighbor) + row->(neighbor.col) + (row.neighbor)->col + (neighbor.row)->col)
    }
    -- If subtraction or division, must be size 2
    cage.operation in Subtraction + Division implies #(cage.cells) = 2
    -- If a singleton, must be addition
    #(cage.cells) = 1 implies cage.operation in Addition
}

pred isWellFormedBoard[board: Board] {
    all cage: Cage | cage in board.cages implies {
        isWellFormedCage[cage]
    }
    all row: Idx | all col: Idx {
        one cells.col.row & board.cages
    }
}

pred isWellFormedSolution[soln: Solution] {
    -- Board is well formed.
    isWellFormedBoard[soln.board]
    -- Board cells equal to the solution cells
    soln.board.cages.cells = soln.values.Int
    -- assert all cells have a value in [1, n]
    all row: Idx | #(soln.values.row.Idx) = #(Idx)
    all col: Idx | #(soln.values.Idx.col) = #(Idx)
    all row: Idx | all col:Idx |
        sol.values.row.col <= #(Idx) and sol.values.row.col > 0
}


pred isSolvedCage[cage: Cage, soln: Solution] {
    -- assert evaluateCage[Cage, Solution] == result
}

pred isSolvedSolution[soln: Solution] {
    -- assert all cells are satisfied
}
-- ====================================================================
-- TESTS (isWellFormedCage)
-- ====================================================================

-- Test on a 1x2 cage.
example StandardCage1 is {all cage: Cage | isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Multiplication0
    cells = Cage0->I10->I10 + Cage0->I20->I10
    result = Cage0->sing[7]
}

-- Test on a 1x2 cage.
example StandardCage1 is {all cage: Cage | isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Multiplication0
    cells = Cage0->I10->I10 + Cage0->I20->I10
    result = Cage0->sing[7]
}

-- Test on a 4-square cage.
example StandardCage2 is {all cage: Cage | isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Multiplication0
    cells = Cage0->I10->I10 + Cage0->I20->I10 + Cage0->I10->I20 + Cage0->I10->I30
    result = Cage0->sing[7]
}

-- Test on a disconnected cage (1,1) + (2, 2)
example Disconnected is {some cage: Cage | not isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Multiplication0
    cells = Cage0->I10->I10 + Cage0->I20->I20
    result = Cage0->sing[7]
}

-- Test that subtraction can't be too big
example SubtractionBig is {some cage: Cage | not isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Subtraction0
    cells = Cage0->I10->I10 + Cage0->I20->I10 + Cage0->I10->I20
    result = Cage0->sing[7]
}

-- Test that division can't be too big
example DivisionBig is {some cage: Cage | not isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Division0
    cells = Cage0->I10->I10 + Cage0->I20->I10 + Cage0->I10->I20
    result = Cage0->sing[7]
}


-- ====================================================================
-- TESTS (isWellFormedBoard)
-- ====================================================================


-- ====================================================================
-- TESTS (isWellFormedSolution)
-- ====================================================================


-- ====================================================================
-- TESTS (isSolvedCage)
-- ====================================================================


-- ====================================================================
-- TESTS (isSolvedSolution)
-- ====================================================================


-- ====================================================================
-- RUN
-- ====================================================================

run {
    isWellFormedIdx
    all c: Cage | isWellFormedCage[c]
} for exactly 1 Cage, 0 Solution, 0 Board
