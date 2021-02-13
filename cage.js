const indexes = [I1, I2, I3, I4]
const idxToInt = (idx) => indexes.findIndex((i) => i.equals(idx))
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
    const rowIdx = idxToInt(row),
      colIdx = idxToInt(col)
    if (cageArray[rowIdx][colIdx] != null) {
      throw new Error(`Dupe at ${rowIdx + 1}, ${colIdx + 1}: Cage${i} and Cage${cageArray[rowIdx][colIdx].i}`)
    }
    debugger
    cageArray[rowIdx][colIdx] = { i, op: labels.get(unwrap(cage.join(operation))) }
  }
})
const table = document.createElement('table')
const colors = ['#B10DC9', '#0074D9', '#2ECC40', '#85144b']
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
div.innerHTML = ''
div.appendChild(table)


