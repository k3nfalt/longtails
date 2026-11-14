const fs = require('node:fs');
const {mathjax} = require('mathjax-full/js/mathjax.js');
const {TeX} = require('mathjax-full/js/input/tex.js');
const {CHTML} = require('mathjax-full/js/output/chtml.js');
const {AllPackages} = require('mathjax-full/js/input/tex/AllPackages.js');
const {liteAdaptor} = require('mathjax-full/js/adaptors/liteAdaptor.js');
const {RegisterHTMLHandler} = require('mathjax-full/js/handlers/html.js');
const {AssistiveMmlHandler} = require('mathjax-full/js/a11y/assistive-mml.js');

const data = JSON.parse(fs.readFileSync(0, 'utf8'));
const fragments = [];
function collect(value) {
  if (!value || typeof value !== 'object') return;
  for (const [key, item] of Object.entries(value)) {
    if (key.endsWith('Html') && typeof item === 'string') fragments.push([value, key]);
    else collect(item);
  }
}
collect(data);

const adaptor = liteAdaptor();
AssistiveMmlHandler(RegisterHTMLHandler(adaptor));
const output = new CHTML({fontURL: 'mathjax-fonts'});
const document = mathjax.document(fragments.map(([value, key]) => `<div>${value[key]}</div>`).join(''), {
  InputJax: new TeX({packages: AllPackages.filter(name => !['autoload', 'require', 'noerrors', 'noundefined'].includes(name)),
    macros: {allowbreak: '', relax: ''},
    formatError: (_jax, error) => { throw error; }}),
  OutputJax: output,
  compileError: (_document, math, error) => { throw new Error(`Invalid TeX: ${math.math}`, {cause: error}); },
  typesetError: (_document, math, error) => { throw new Error(`Cannot render: ${math.math}`, {cause: error}); },
});
const body = adaptor.body(document.document);
for (const span of adaptor.tags(body, 'span')) {
  if (adaptor.hasClass(span, 'math')) adaptor.setAttribute(span, 'data-tex', adaptor.textContent(span));
}
document.render();
adaptor.childNodes(body).forEach((node, index) => {
  const [value, key] = fragments[index];
  value[key] = adaptor.innerHTML(node);
});
const css = adaptor.textContent(output.styleSheet(document));
process.stdout.write(JSON.stringify({data, css}));
