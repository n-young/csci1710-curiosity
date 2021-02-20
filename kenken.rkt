#lang forge

-- ====================================================================
-- SIGNATURES
-- ====================================================================

abstract sig Idx {
    neighbor: lone Idx
}
one sig I1, I2, I3, I4 extends Idx {}
pred isWellFormedIdx { neighbor = I1->I2 + I2->I3 + I3->I4 }

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
    -- There are at least some cells
    #(cage.cells) > 0
    #(cage.cells) <= 3
    -- If a singleton, must be addition
    #(cage.cells) = 1 implies cage.operation in Addition
    -- assert all cells are adjacent; if sub or div, max 2 cells
    #(cage.cells) > 1 implies {all row: Idx | all col: Idx | row->col in cage.cells implies {
        some cage.cells & (row->(col.neighbor) + row->(neighbor.col) + (row.neighbor)->col + (neighbor.row)->col)
    }}
    -- If subtraction or division, must be size 2
    cage.operation in Subtraction + Division implies #(cage.cells) = 2
}

pred isWellFormedBoard[board: Board] {
    all cage: Cage | cage in board.cages implies {
        isWellFormedCage[cage]
    }
    all row: Idx | all col: Idx {
        one (cells.row.col & board.cages)
    }
}

pred isSolution[soln: Solution] {
    -- Board is well formed.
    isWellFormedBoard[soln.board]
    -- Board cells equal to the solution cells
    soln.board.cages.cells = soln.values.Int
    -- assert all cells have a value in [1, n] with every valid value present in each row and column
    all num: Int | num > 0 and num <= #(Idx) implies {
        all row: Idx | one col: Idx {
            soln.values.row.col = num
        }
        all col: Idx | one row: Idx {
            soln.values.row.col = num
        }
    }
}


pred isSolvedCage[cage: Cage, soln: Solution] {
    -- assert evaluateCage[Cage, Solution] == result
}

-- ====================================================================
-- TESTS (isWellFormedCage)
-- ====================================================================

-- Test on a 1x2 cage.
example StandardCage1 is {all cage: Cage | isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Multiplication0
    cells = Cage0->(I10->I10 + I20->I10)
    result = Cage0->sing[7]
}
-- Test on a 4-square cage.
example StandardCage2 is {all cage: Cage | isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Multiplication0
    cells = Cage0->(I10->I10 + I20->I10 + I10->I20 + I10->I30)
    result = Cage0->sing[7]
}

-- Test on a disconnected cage (1,1) + (2, 2)
example Disconnected is {some cage: Cage | not isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Multiplication0
    cells = Cage0->(I10->I10 + I20->I20)
    result = Cage0->sing[7]
}

-- Test that subtraction can't be too big
example SubtractionBig is {some cage: Cage | not isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Subtraction0
    cells = Cage0->(I10->I10 + I20->I10 + I10->I20)
    result = Cage0->sing[7]
}

-- Test that division can't be too big
example DivisionBig is {some cage: Cage | not isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Division0
    cells = Cage0->(I10->I10 + I20->I10 + I10->I20)
    result = Cage0->sing[7]
}

-- ====================================================================
-- TESTS (isWellFormedBoard)
-- ====================================================================

-- 4x4 normal board
example NormalBoard is {all board: Board | isWellFormedBoard[board]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0 + Cage1 + Cage2 + Cage3 + Cage4 + Cage5 + Cage6 + Cage7
    cages = Board0->(Cage0 + Cage1 + Cage2 + Cage3 + Cage4 + Cage5 + Cage6 + Cage7)
    operation = Cage0->Division0 + Cage1->Addition0 + Cage2->Addition0 + Cage3->Subtraction0
    + Cage4->Subtraction0 + Cage5->Multiplication0 + Cage6->Subtraction0 + Cage7->Subtraction0
    cells = Cage0->(I10->I10 + I10->I20) + Cage1->(I10->I30 + I20->I30) + Cage2->I10->I40
    + Cage3->(I20->I10 + I30->I10) + Cage4->(I20->I20 + I30->I20) + Cage5->(I30->I30 + I40->I30 + I40->I40)
    + Cage6->(I20->I40 + I30->I40) + Cage7->(I40->I10 + I40->I20)
    result = Cage0->sing[2] + Cage1->sing[7] + Cage2->sing[4] + Cage3->sing[1] + Cage4->sing[3]
    + Cage5->sing[4] + Cage6->sing[2] + Cage7->sing[1]
}

-- ====================================================================
-- TESTS (isSolution)
-- ====================================================================


-- ====================================================================
-- TESTS (isSolvedCage)
-- ====================================================================


-- ====================================================================
-- RUN
-- ====================================================================

run {
    isWellFormedIdx
    some b: Board | {
        isWellFormedBoard[b]
        all c: Cage | c in b.cages
    }
   -- Addition + Subtraction + Multiplication + Division in Cage.operation
} for exactly 6 Int, exactly 0 Solution, exactly 1 Board, exactly 8 Cage
