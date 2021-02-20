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
-- FUNCTIONS
-- ====================================================================

// TODO: Worry about duplicate values in a sol
fun evaluateCageAddition[cage: Cage, soln: Solution]: Int {
    add[((cage.cells)->Int & soln.values)[Idx, Idx]]
}
pred checkCageSubtraction[cage: Cage, soln: Solution] {
    some row, col: Idx | row->col in cage.cells and {
        some otherRow, otherCol: Idx | {
            otherRow->otherCol in cage.cells
            row != otherRow
            col != otherCol
            subtract[solution.values.row.col, solution.values.otherRow.otherCol] = cage.result
        }
    }
}
fun evaluateCageMultiplication[cage: Cage, soln: Solution]: Int {
    multiply[((cage.cells)->Int & soln.values)[Idx, Idx]]
}
fun evaluateCageDivision[cage: Cage, soln: Solution]: Int {
    divide[((cage.cells)->Int & soln.values)[Idx, Idx]]
}


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

pred isWellFormedSolution[soln: Solution] {
    -- Board is well formed.
    isWellFormedBoard[soln.board]
    -- Board cells equal to the solution cells
    soln.board.cages.cells = soln.values.Int
    -- assert all cells have a value in [1, n] with every valid value present in each row and column
    all num: Int | sum[num] > 0 and sum[num] <= #(Idx) implies {
        all row: Idx | one col: Idx {
            soln.values[row, col] = num
        }
        all col: Idx | one row: Idx {
            soln.values[row, col] = num
        }
    }
}

pred isSolved[soln: Solution] {
    -- Is a well formed solution
    isWellFormedSolution[soln]
    -- All cages evaluate properly
    all c: Cage | c in soln.board.cages implies {
        checkCageSubtraction[c, soln]
        /*
        c.operation in Addition implies sum[c.result] = evaluateCageAddition[c, soln]
        else c.operation in Subtraction implies sum[c.result] = evaluateCageSubtraction[c, soln]
        else c.operation in Multiplication implies sum[c.result] = evaluateCageMultiplication[c, soln]
        else c.operation in Division implies sum[c.result] = evaluateCageDivision[c, soln]*/
    }
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
-- Test on a 3-cell cage.
example StandardCage2 is {all cage: Cage | isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Multiplication0
    cells = Cage0->(I10->I10 + I10->I20 + I10->I30)
    result = Cage0->sing[7]
}
-- Test on a 1-cell cage.
example StandardCage3 is {all cage: Cage | isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Addition0
    cells = Cage0->I10->I10
    result = Cage0->sing[7]
}
-- Test on a 1-cell cage.
example Invalid1CellOp is {no cage: Cage | isWellFormedCage[cage]} for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Division0
    cells = Cage0->I10->I10
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
-- TESTS (isWellFormedSolution)
-- ====================================================================


-- ====================================================================
-- TESTS (isSolvedCage)
-- ====================================================================

// example NormalSolution is {all board: Board | isWellFormedBoard[board]} for {
//     neighbor = I10->I20 + I20->I30 + I30->I40
//     Cage = Cage0 + Cage1 + Cage2 + Cage3 + Cage4 + Cage5 + Cage6 + Cage7
//     cages = Board0->(Cage0 + Cage1 + Cage2 + Cage3 + Cage4 + Cage5 + Cage6 + Cage7)
//     operation = Cage0->Division0 + Cage1->Addition0 + Cage2->Addition0 + Cage3->Subtraction0
//     + Cage4->Subtraction0 + Cage5->Multiplication0 + Cage6->Subtraction0 + Cage7->Subtraction0
//     cells = Cage0->(I10->I10 + I10->I20) + Cage1->(I10->I30 + I20->I30) + Cage2->I10->I40
//     + Cage3->(I20->I10 + I30->I10) + Cage4->(I20->I20 + I30->I20) + Cage5->(I30->I30 + I40->I30 + I40->I40)
//     + Cage6->(I20->I40 + I30->I40) + Cage7->(I40->I10 + I40->I20)
//     result = Cage0->sing[2] + Cage1->sing[7] + Cage2->sing[4] + Cage3->sing[1] + Cage4->sing[3]
//     + Cage5->sing[4] + Cage6->sing[2] + Cage7->sing[1]
//     board = Solution0->Board0
//     values = Solution0->()
// }


-- ====================================================================
-- RUN
-- ====================================================================

run {
    isWellFormedIdx
    all s: Solution | isWellFormedSolution[s]
} for exactly 6 Int, exactly 1 Solution, exactly 1 Board, exactly 7 Cage
