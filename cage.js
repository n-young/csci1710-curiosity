const indexes = [I1, I2, I3, I4]
const idxToNumber = idx => indexes.findIndex(i => i.equals(idx))
const intToNumber = int => parseInt(int.toString())
const labels = new Map([
  [Addition0, '+'],
  [Subtraction0, '-'],
  [Multiplication0, '×'],
  [Division0, '÷'],
])

const unwrap = v => v.tuples()[0].atoms()[0]

const cageArray = Array(indexes.length)
  .fill()
  .map(() => Array(indexes.length).fill())
Cage.atoms().forEach((cage, i) => {
  for (const cell of cage.join(cells).tuples()) {
    const [row, col] = cell.atoms()
    const rowIdx = idxToNumber(row),
      colIdx = idxToNumber(col)
    if (cageArray[rowIdx][colIdx] != null) {
      throw new Error(
        `Dupe at ${rowIdx + 1}, ${colIdx + 1}: Cage${i} and Cage${
          cageArray[rowIdx][colIdx].i
        }`
      )
    }
    cageArray[rowIdx][colIdx] = {
      i,
      op: labels.get(unwrap(cage.join(operation))),
    }
  }
})
const table = document.createElement('table')
const colors = [
  '#B10DC9',
  '#0074D9',
  '#2ECC40',
  '#85144b',
  '#39CCCC',
  '#FF851B',
  '#FF4136',
  '#AAAAAA',
]
for (const row of cageArray) {
  const tr = document.createElement('tr')
  table.appendChild(tr)
  for (const col of row) {
    const td = document.createElement('td')
    tr.appendChild(td)
    td.textContent = col?.op
    td.style.backgroundColor = col != null ? colors[col.i] : 'transparent'
    td.style.textAlign = 'center'
    td.style.color = 'white'
    td.style.width = '20px'
    td.style.height = '20px'
    td.style.border = 'none'
  }
}
table.style.border = '1px solid black'
table.style.margin = '1em'

const solutionValues = Array(indexes.length)
  .fill()
  .map(() => Array(indexes.length).fill())
for (const cell of Solution0.join(values).tuples()) {
  const [row, col, value] = cell.atoms()
  const rowIdx = idxToNumber(row),
    colIdx = idxToNumber(col)
  if (solutionValues[rowIdx][colIdx] != null) {
    throw new Error(
      `Dupe at ${rowIdx + 1}, ${colIdx + 1}: ${value} and ${
        solutionValues[rowIdx][colIdx]
      }`
    )
  }
  solutionValues[rowIdx][colIdx] = intToNumber(value)
}
const table2 = document.createElement('table')
for (const row of solutionValues) {
  const tr = document.createElement('tr')
  table2.appendChild(tr)
  for (const col of row) {
    const td = document.createElement('td')
    tr.appendChild(td)
    td.textContent = col
    td.style.textAlign = 'center'
    td.style.width = '22px'
    td.style.height = '2px'
    td.style.border = '1px solid black'
  }
}
table2.style.margin = '1em'
table2.style.borderCollapse = 'collapse'

div.innerHTML = ''
div.appendChild(table)
div.appendChild(table2)

