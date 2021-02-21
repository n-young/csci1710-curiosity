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

const cageValues = []
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
    const cageInfo = {
      i,
      op: labels.get(unwrap(cage.join(operation))),
      val: intToNumber(unwrap(cage.join(result))),
    }
    cageValues[i] = cageInfo
    cageArray[rowIdx][colIdx] = cageInfo
  }
})
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

const valuesList = document.createElement('table')
cageValues.forEach(({ val, op }, i) => {
  const tr = document.createElement('tr')
  tr.style.backgroundColor = colors[i]
  tr.style.color = 'white'
  tr.innerHTML = `<td>${val}</td><td>${op}</td>`
  ;[...tr.children].forEach(c => (c.style.padding = '2px 8px'))
  valuesList.appendChild(tr)
})
valuesList.style.float = 'left'
valuesList.style.margin = '1em'
valuesList.style.marginRight = '0.5em'
valuesList.style.padding = '0'
valuesList.style.borderCollapse = 'collapse'

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
        solutionValues[rowIdx][colIdx].value
      }`
    )
  }
  solutionValues[rowIdx][colIdx] = {
    value: intToNumber(value),
    i: cageArray[rowIdx][colIdx]?.i,
  }
}
const table = document.createElement('table')
for (const row of solutionValues) {
  const tr = document.createElement('tr')
  table.appendChild(tr)
  for (const { value, i } of row) {
    const td = document.createElement('td')
    tr.appendChild(td)
    td.textContent = value
    td.style.background = colors[i]
    td.style.textAlign = 'center'
    td.style.width = '32px'
    td.style.height = '32px'
    td.style.color = 'white'
  }
}
table.style.border = '1px solid black'
table.style.margin = 'calc(1em + 1px)'
table.style.float = 'left'

div.innerHTML = ''
div.appendChild(valuesList)
div.appendChild(table)

