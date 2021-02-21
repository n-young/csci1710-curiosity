#lang forge

-- ====================================================================
-- SIGNATURES
-- ====================================================================

abstract sig Idx {
    neighbor: lone Idx
}
one sig I1, I2, I3, I4 extends Idx {}
pred isWellFormedIdx { neighbor = I1->I2 + I2->I3 + I3->I4 }

abstract sig Operation {}
one sig Addition extends Operation {}
one sig Subtraction extends Operation {}
one sig Multiplication extends Operation {}
one sig Division extends Operation {}

sig Cage {
    operation: one Operation,
    cells: set Idx->Idx,
    result: one Int
}

sig Board {
    cages: set Cage
}

sig Solution {
    board: one Board,
    values: set Idx->Idx->Int
}


-- ====================================================================
-- PREDICATES
-- ====================================================================

pred isWellFormedCage[cage: Cage] {
    -- There are at least some cells, but not more than 3.
    #(cage.cells) > 0
    #(cage.cells) <= 3
    -- All cells are connected.
    #(cage.cells) > 1 implies {all row: Idx | all col: Idx | row->col in cage.cells implies {
        some cage.cells & (row->(col.neighbor) + row->(neighbor.col) + (row.neighbor)->col + (neighbor.row)->col)
    }}
    -- If a singleton, must be addition.
    #(cage.cells) = 1 implies cage.operation in Addition
    -- If subtraction or division, must have exactly 2 cells.
    cage.operation in (Subtraction + Division) implies #(cage.cells) = 2
}

pred isWellFormedBoard[board: Board] {
    -- All cages are well formed.
    all cage: Cage | cage in board.cages implies isWellFormedCage[cage]
    -- Each square is in a single cage.
    all row: Idx | all col: Idx | one (cells.row.col & board.cages)
}

pred isWellFormedSolution[soln: Solution] {
    -- Board is well formed.
    isWellFormedBoard[soln.board]
    -- Board cells equal to the solution cells.
    soln.board.cages.cells = soln.values.Int
    -- All cells have a value in [1, n] with every value present in each row and column.
    all num: Int | sum[num] > 0 and sum[num] <= #(Idx) implies {
        all row: Idx | one col: Idx | soln.values[row, col] = num
        all col: Idx | one row: Idx | soln.values[row, col] = num
    }
    -- Each cage has distinct values.
    all c: Cage | c in soln.board.cages implies {
        #c.cells = #((c.cells)->Int & soln.values)[Idx, Idx]
    }
}

pred isSolvedCage[c: Cage, soln: Solution] {
    -- Depending on the operation, evaluates correctly.
    let cageValues = ((c.cells)->Int & soln.values)[Idx, Idx] | {
        c.operation in Addition implies sum[c.result] = sum[cageValues]
        else c.operation in Subtraction implies sum[c.result] = subtract[max[cageValues], min[cageValues]]
        else c.operation in Multiplication implies {
            #(cageValues) = 2 implies sum[c.result] = multiply[max[cageValues], min[cageValues]]
            #(cageValues) = 3 implies {
                let maxValue = max[cageValues] | {
                    let withoutMax = cageValues - sing[maxValue] | {
                        sum[c.result] = multiply[maxValue, max[withoutMax], min[withoutMax]]
                    }
                }
            }
        }
        else c.operation in Division implies multiply[min[cageValues], sum[c.result]] = max[cageValues]
    }
}

pred isSolvedBoard[soln: Solution] {
    -- Is a well formed solution.
    isWellFormedSolution[soln]
    -- All cages evaluate properly.
    all c: Cage | c in soln.board.cages implies isSolvedCage[c, soln]
}


-- ====================================================================
-- TESTS (isWellFormedCage)
-- ====================================================================

-- Test on a 1-cell cage.
example StandardCage3 is { all cage: Cage | isWellFormedCage[cage] } for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Addition0
    cells = Cage0->I10->I10
    result = Cage0->sing[3]
}

-- Test on a 1x2 cage.
example StandardCage1 is { all cage: Cage | isWellFormedCage[cage] } for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Multiplication0
    cells = Cage0->(I10->I10 + I20->I10)
    result = Cage0->sing[3]
}

-- Test on a 3-cell cage.
example StandardCage2 is { all cage: Cage | isWellFormedCage[cage] } for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Multiplication0
    cells = Cage0->(I10->I10 + I10->I20 + I10->I30)
    result = Cage0->sing[3]
}

-- Test on a 1-cell cage.
example Invalid1CellOp is { no cage: Cage | isWellFormedCage[cage] } for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Division0
    cells = Cage0->I10->I10
    result = Cage0->sing[3]
}

-- Test on a 4-cell cage (too big).
example CageTooBig is { no cage: Cage | isWellFormedCage[cage] } for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Multiplication0
    cells = Cage0->(I10->I10 + I10->I20 + I10->I30 + I10->I40)
    result = Cage0->sing[3]
}

-- Test on a disconnected cage (1,1) + (2, 2)
example Disconnected is { some cage: Cage | not isWellFormedCage[cage] } for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Multiplication0
    cells = Cage0->(I10->I10 + I20->I20)
    result = Cage0->sing[3]
}

-- Test that a singleton must be addition
example DivisionBig is { some cage: Cage | not isWellFormedCage[cage] } for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Division0
    cells = Cage0->(I10->I10)
    result = Cage0->sing[3]
}

-- Test that subtraction can't be too big
example SubtractionBig is { some cage: Cage | not isWellFormedCage[cage] } for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Subtraction0
    cells = Cage0->(I10->I10 + I20->I10 + I10->I20)
    result = Cage0->sing[3]
}

-- Test that division can't be too big
example DivisionBig is { some cage: Cage | not isWellFormedCage[cage] } for {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0
    operation = Cage0->Division0
    cells = Cage0->(I10->I10 + I20->I10 + I10->I20)
    result = Cage0->sing[3]
}


-- ====================================================================
-- TESTS (isSolvedCage)
-- ====================================================================

-- Solved singleton case
inst SingletonSolvedCage {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = C0
    operation = C0->Addition0
    cells = C0->(I10->I10)
    result = C0->sing[3]
    Board = B
    cages = B->C0
    Solution = S
    board = S->B
    values = S->(I10->I10->sing[3])
}
test expect {
    singleton_solved_cage: { all c: Cage | all s: Solution | isWellFormedCage[c] and isSolvedCage[c, s] }
        for exactly 6 Int for SingletonSolvedCage is sat
}

-- Solved 2-addition cage
inst Addition2SolvedCage {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = C0
    operation = C0->Addition0
    cells = C0->(I10->I10 + I10->I20)
    result = C0->sing[5]
    Board = B
    cages = B->C0
    Solution = S
    board = S->B
    values = S->(I10->I10->sing[3] + I10->I20->sing[2])
}
test expect {
    addition_2_solved_cage: { all c: Cage | all s: Solution | isWellFormedCage[c] and isSolvedCage[c, s] }
        for exactly 6 Int for Addition2SolvedCage is sat
}

-- Solved 3-addition cage
inst Addition3SolvedCage {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = C0
    operation = C0->Addition0
    cells = C0->(I10->I10 + I10->I20 + I10->I30)
    result = C0->sing[6]
    Board = B
    cages = B->C0
    Solution = S
    board = S->B
    values = S->(I10->I10->sing[3] + I10->I20->sing[2] + I10->I30->sing[1])
}
test expect {
    addition_3_solved_cage: { all c: Cage | all s: Solution | isWellFormedCage[c] and isSolvedCage[c, s] }
        for exactly 6 Int for Addition3SolvedCage is sat
}

-- Solved 2-subtraction cage
inst Subtraction2SolvedCage {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = C0
    operation = C0->Subtraction0
    cells = C0->(I10->I10 + I10->I20)
    result = C0->sing[1]
    Board = B
    cages = B->C0
    Solution = S
    board = S->B
    values = S->(I10->I10->sing[3] + I10->I20->sing[2])
}
test expect {
    subtraction_2_solved_cage: { all c: Cage | all s: Solution | isWellFormedCage[c] and isSolvedCage[c, s] }
        for exactly 6 Int for Subtraction2SolvedCage is sat
}

-- Solved 2-multiplication cage
inst Multiplication2SolvedCage {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = C0
    operation = C0->Multiplication0
    cells = C0->(I10->I10 + I10->I20)
    result = C0->sing[6]
    Board = B
    cages = B->C0
    Solution = S
    board = S->B
    values = S->(I10->I10->sing[3] + I10->I20->sing[2])
}
test expect {
    multiplication_2_solved_cage: { all c: Cage | all s: Solution | isWellFormedCage[c] and isSolvedCage[c, s] }
        for exactly 6 Int for Multiplication2SolvedCage is sat
}

-- Solved 3-multiplication cage
inst Multiplication3SolvedCage {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = C0
    operation = C0->Multiplication0
    cells = C0->(I10->I10 + I10->I20 + I10->I30)
    result = C0->sing[12]
    Board = B
    cages = B->C0
    Solution = S
    board = S->B
    values = S->(I10->I10->sing[3] + I10->I20->sing[4] + I10->I30->sing[1])
}
test expect {
    multiplication_3_solved_cage: { all c: Cage | all s: Solution | isWellFormedCage[c] and isSolvedCage[c, s] }
        for exactly 6 Int for Multiplication3SolvedCage is sat
}

-- Solved 2-division cage
inst Division2SolvedCage {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = C0
    operation = C0->Division0
    cells = C0->(I10->I10 + I10->I20)
    result = C0->sing[3]
    Board = B
    cages = B->C0
    Solution = S
    board = S->B
    values = S->(I10->I10->sing[6] + I10->I20->sing[2])
}
test expect {
    division_2_solved_cage: { all c: Cage | all s: Solution | isWellFormedCage[c] and isSolvedCage[c, s] }
        for exactly 6 Int for Division2SolvedCage is sat
}

-- Division isn't integer division
inst NotIntegerDivisionCage {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = C0
    operation = C0->Division0
    cells = C0->(I10->I10 + I10->I20)
    result = C0->sing[2]
    Board = B
    cages = B->C0
    Solution = S
    board = S->B
    values = S->(I10->I10->sing[5] + I10->I20->sing[2])
}
test expect {
    not_integer_division: { no c: Cage | all s: Solution | isWellFormedCage[c] and isSolvedCage[c, s] }
        for exactly 6 Int for NotIntegerDivisionCage is sat
}

-- Can't handle duplicate values
inst DupeValsSolvedCage {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = C0
    operation = C0->Multiplication0
    cells = C0->(I10->I10 + I10->I20 + I10->I30)
    result = C0->sing[12]
    Board = B
    cages = B->C0
    Solution = S
    board = S->B
    values = S->(I10->I10->sing[3] + I10->I20->sing[2] + I10->I30->sing[2])
}
test expect {
    dupe_vals_solved_cage: { no c: Cage | all s: Solution | isWellFormedCage[c] and isSolvedCage[c, s] }
        for exactly 6 Int for DupeValsSolvedCage is sat
}


-- ====================================================================
-- TESTS (isWellFormedBoard, isWellFormedSolution, isSolvedBoard)
-- ====================================================================

-- solution
inst Solution0 {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0 + Cage1 + Cage2 + Cage3 + Cage4 + Cage5 + Cage6
    cages = Board0->(Cage0 + Cage1 + Cage2 + Cage3 + Cage4 + Cage5 + Cage6)
    operation = Cage0->Division0 + Cage1->Multiplication0 + Cage2->Multiplication0 + Cage3->Multiplication0
        + Cage4->Multiplication0 + Cage5->Addition0 + Cage6->Multiplication0
    cells = Cage0->(I10->I10 + I10->I20)
        + Cage1->(I10->I30 + I10->I40)
        + Cage2->(I20->I10 + I20->I20)
        + Cage3->(I20->I30 + I20->I40 + I30->I30)
        + Cage4->(I30->I10 + I30->I20 + I40->I10)
        + Cage5->(I30->I40)
        + Cage6->(I40->I20 + I40->I30 + I40->I40)
    result = Cage0->sing[4] + Cage1->sing[6] + Cage2->sing[8] + Cage3->sing[6] + Cage4->sing[6]
        + Cage5->sing[4] + Cage6->sing[12]
    board = Solution0->Board0
    values = Solution0->(
          I10->I10->sing[1] + I10->I20->sing[4] + I10->I30->sing[3] + I10->I40->sing[2]
        + I20->I10->sing[4] + I20->I20->sing[2] + I20->I30->sing[1] + I20->I40->sing[3]
        + I30->I10->sing[3] + I30->I20->sing[1] + I30->I30->sing[2] + I30->I40->sing[4]
        + I40->I10->sing[2] + I40->I20->sing[3] + I40->I30->sing[4] + I40->I40->sing[1])
}
test expect {
    sol0_wfb: { isWellFormedIdx all b: Board | isWellFormedBoard[b] } for exactly 6 Int for Solution0 is sat
    sol0_wfs: { isWellFormedIdx all s: Solution | isWellFormedSolution[s] } for exactly 6 Int for Solution0 is sat
    sol0_solved: { isWellFormedIdx all s: Solution | isSolvedBoard[s] } for exactly 6 Int for Solution0 is sat
}

-- solution
inst Solution1 {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0 + Cage1 + Cage2 + Cage3 + Cage4 + Cage5 + Cage6
    cages = Board0->(Cage0 + Cage1 + Cage2 + Cage3 + Cage4 + Cage5 + Cage6)
    operation = Cage0->Multiplication0 + Cage1->Addition0 + Cage2->Addition0 + Cage3->Addition0
        + Cage4->Subtraction0 + Cage5->Multiplication0 + Cage6->Addition0
    cells = Cage0->(I10->I10 + I10->I20 + I10->I30)
        + Cage1->(I10->I40)
        + Cage2->(I20->I10 + I30->I10 + I40->I10)
        + Cage3->(I20->I20 + I30->I20 + I40->I20)
        + Cage4->(I20->I30 + I30->I30)
        + Cage5->(I20->I40 + I30->I40 + I40->I40)
        + Cage6->(I40->I30)
    result = Cage0->sing[24] + Cage1->sing[1] + Cage2->sing[7] + Cage3->sing[8] + Cage4->sing[2]
        + Cage5->sing[24] + Cage6->sing[2]
    board = Solution0->Board0
    values = Solution0->(
          I10->I10->sing[3] + I10->I20->sing[2] + I10->I30->sing[4] + I10->I40->sing[1]
        + I20->I10->sing[2] + I20->I20->sing[4] + I20->I30->sing[1] + I20->I40->sing[3]
        + I30->I10->sing[4] + I30->I20->sing[1] + I30->I30->sing[3] + I30->I40->sing[2]
        + I40->I10->sing[1] + I40->I20->sing[3] + I40->I30->sing[2] + I40->I40->sing[4])
}
test expect {
    sol1_wfb: { isWellFormedIdx all b: Board | isWellFormedBoard[b] } for exactly 6 Int for Solution1 is sat
    sol1_wfs: { isWellFormedIdx all s: Solution | isWellFormedSolution[s] } for exactly 6 Int for Solution1 is sat
    sol1_solved: { isWellFormedIdx all s: Solution | isSolvedBoard[s] } for exactly 6 Int for Solution1 is sat
}

-- solution with nondistinct cage values
inst NondistinctCageSolution {
    neighbor = I10->I20 + I20->I30 + I30->I40
    Cage = Cage0 + Cage1 + Cage2 + Cage3 + Cage4 + Cage5 + Cage6 + Cage7
    cages = Board0->(Cage0 + Cage1 + Cage2 + Cage3 + Cage4 + Cage5 + Cage6 + Cage7)
    operation = Cage0->Division0 + Cage1->Addition0 + Cage2->Addition0 + Cage3->Subtraction0
        + Cage4->Subtraction0 + Cage5->Multiplication0 + Cage6->Subtraction0 + Cage7->Subtraction0
    cells = Cage0->(I10->I10 + I10->I20)
        + Cage1->(I10->I30 + I20->I30)
        + Cage2->I10->I40
        + Cage3->(I20->I10 + I30->I10)
        + Cage4->(I20->I20 + I30->I20)
        + Cage5->(I30->I30 + I40->I30 + I40->I40)
        + Cage6->(I20->I40 + I30->I40)
        + Cage7->(I40->I10 + I40->I20)
    result = Cage0->sing[2] + Cage1->sing[7] + Cage2->sing[4] + Cage3->sing[1] + Cage4->sing[3]
        + Cage5->sing[4] + Cage6->sing[2] + Cage7->sing[1]
    board = Solution0->Board0
    values = Solution0->(
        I10->I10->sing[1] + I10->I20->sing[2] + I10->I30->sing[3] + I10->I40->sing[4]
        + I20->I10->sing[2] + I20->I20->sing[1] + I20->I30->sing[4] + I20->I40->sing[3]
        + I30->I10->sing[3] + I30->I20->sing[4] + I30->I30->sing[2] + I30->I40->sing[1]
        + I40->I10->sing[4] + I40->I20->sing[3] + I40->I30->sing[1] + I40->I40->sing[2])
}
// test expect {
//     nondistinct_wfb: { isWellFormedIdx no b: Board | isWellFormedBoard[b] } for exactly 6 Int for NondistinctCageSolution is sat
//     nondistinct_wfs: { isWellFormedIdx no s: Solution | isWellFormedSolution[s] } for exactly 6 Int for NondistinctCageSolution is sat
//     nondistinct_solved: { isWellFormedIdx no s: Solution | isSolvedBoard[s] } for exactly 6 Int for NondistinctCageSolution is sat
// }


-- ====================================================================
-- RUN
-- ====================================================================

run {
    isWellFormedIdx
    all s: Solution | isSolvedBoard[s]
} for exactly 6 Int, exactly 1 Solution, exactly 1 Board, exactly 7 Cage
