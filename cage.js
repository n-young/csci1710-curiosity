const indexes = [I1, I2, I3, I4]
const idxToInt = (idx) => indexes.findIndex((i) => i.equals(idx))

const cageArray = Array(indexes.length)
  .fill()
  .map(() => Array(indexes.length).fill())
Cage.atoms().forEach((cage, i) => {
  for (const cell of cage.join(cells).tuples()) {
    const [row, col] = cell.atoms()
    cageArray[idxToInt(row)][idxToInt(col)] = i
  }
})
const table = document.createElement('table')
const colors = ['#B10DC9', '#0074D9', '#2ECC40', '#FFDC00']
for (const row of cageArray) {
  const tr = document.createElement('tr')
  table.appendChild(tr)
  for (const col of row) {
    const td = document.createElement('td')
    tr.appendChild(td)
    td.style.backgroundColor = col != null ? colors[col] : 'transparent'
    td.style.width = '20px'
    td.style.height = '20px'
    td.style.border = 'none'
  }
}
table.style.border = '1px solid black'
table.style.margin = '1em'
div.innerHTML = ''
div.appendChild(table)


