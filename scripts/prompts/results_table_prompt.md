Create ONE concise, includable LaTeX comparison table for the supplied setup and
its supplied theorems. Use the existing reviews as evidence. This is an editorial
task: web access is allowed only to verify references already cited in the reviews
and complete their bibliographic metadata. Do not conduct new literature research,
audit proofs, build Lean, or run other agents. Read the setup to state shared assumptions;
consult theorem statements or descriptions only to clarify formulas or notation.

Read `scripts/negative_examples.md`: its user-reviewed NO IMPROVEMENT assessments override the older verdicts for sorting. Preserve the supported comparison details and qualifications without displaying verdicts.

Read `scripts/positive_examples.md` for user-selected successful attempts and their concrete gains and limitations. Use these alongside the negative examples; preserve the stated regimes and distinguish complexity, scope, oracle, and adaptivity improvements without automatically assigning a verdict or star rating.

GROUPING AND CONTENT

- The supplied list defines exact setup membership. Include every listed theorem
  exactly once, in its own row. Do not combine related but different setup files.
- Put our results first, ordered by reported contribution, then separate prior-work
  rows. Include known results as well as new ones. Do not invent a supplementary
  table, hide weaker results, or claim all tables fit on one page.
- Preserve each review's factual comparisons; use its novelty verdict only for sorting. A broader setup,
  weaker assumptions, improved complexity, reduced oracle requirements, adaptivity,
  stronger output guarantee, new method-specific analysis, and formalization are
  distinct contributions. Keep every supported type visible in the comparison
  text, using short labels such as `Scope:`, `Rate:`, or `Adaptivity:` when helpful;
  do not add a column. Preserve the stated baseline, regime and uncertainty.
  Do not turn a scope extension into a rate improvement, a method-specific advance
  into a problem-class improvement, or a known-rate formalization into new theory.
  Do not upgrade or downgrade the verdict because one comparison row has no gain
  or because the contribution is not a better leading complexity exponent. If
  a review is inconsistent, omit the unsupported comparison rather than adding an opinion.
  Infer types only from explicit claims in the review, not from
  the theorem's name or the table's appearance.
- Select the closest baseline and additional baselines needed to expose distinct
  material gains. Give each baseline its own row; consolidate equivalent ones.
  Each comparison must use the exact guarantee cited in that row. Do not borrow
  an adaptivity, accuracy, or scope advantage from a different theorem in the
  same paper; give that materially different guarantee its own numbered row.
- Distinguish direct competitors from special-case baselines. If a baseline
  cannot solve the full target setup, label its row with the precise restriction
  under which it applies. Describe broader scope as a scope extension; compare
  rates, oracle access and disadvantages only after restricting both results to
  their common setup. Reevaluate required operations on that restriction: an
  operation that becomes an identity, a closed-form update, or unnecessary is
  not an extra oracle-access requirement there. Do not call the machinery needed
  for a broader problem a disadvantage against a method that cannot solve it.
  If the reviews do not establish a common setup or a valid reduction, state
  that the rates are not comparable; do not invent a tradeoff. Prefer a direct
  competitor when assessing performance on the full target setup.
- Compare proved guarantees, in common initial parameters and the same accuracy
  criterion where justified. Count every primitive oracle call, including batches,
  trials and skipped transitions. Distinguish different oracles and outputs.
- Express complexity bounds in big-O notation, using `\mathcal{O}(\cdot)`, with
  one total-cost formula per row where possible. Omit absolute numerical constants,
  including constant factors inside logarithms, and harmless rounding whenever
  this preserves the bound up to universal factors on its stated domain. Keep
  all parameter dependence and terms needed to prevent vanishing or invalid
  bounds (e.g. use `1 + log` or `log_+` where needed). Do not reproduce the full
  iteration-by-iteration convergence bound when a total-cost formula and a short
  accuracy-floor condition suffice.
- Preserve parameter powers, essential logarithms, initialization/noise terms,
  admissibility restrictions and uncertainty affecting a claim. Do not assert
  uniform dominance from a conditional gain. Account for relationships between
  parameters before declaring one displayed term asymptotically worse.
- Prioritize new oracle-complexity guarantees and meaningful problem setups when
  explaining significance. Artificially fixing a method does not make a weaker
  result competitive. An occasional significant exception is a new proof that GD
  can be almost as fast as AGD under comparable assumptions, oracle access, and
  accuracy. State the remaining gap, regimes, and tradeoffs; distinguish this
  method-specific advance from improved problem-class complexity. Popularity
  and use of `allowedAlgorithm` alone do not establish significance. Preserve
  supported comparisons and review verdicts rather than applying this as an
  automatic rating rule.
- Example: `KnownValueSmoothConvexLocalLinear` previously enforced the exact
  SplitBrox implementation through `allowedAlgorithm`. We removed this artificial
  restriction: the setup now specifies the problem and oracle access, while its
  theorem still constructs SplitBrox and proves the same budget.
- `allowedAlgorithm` is optional by default and required only for contributions
  specifically about very popular families such as GD, SGD, or Adam. Occasional use
  for other families is encouraged when it adds useful precision; its absence
  there is not a defect. Distinguish the constructed algorithm from restrictions
  encoded in the setup: check `allowedAlgorithm` before saying the setup requires
  a method or output rule. Names and review descriptions do not establish it.
- Distinguish an improved method-specific theorem from improved problem-class
  complexity. A bound's accuracy floor is not an impossibility lower bound.
  Formalizing a known rate is not a new mathematical rate. Do not introduce
  speculation about practical performance when comparing proved results.

LAYOUT AND STYLE

1. Use portrait orientation, booktabs rules and a wrapping tabularx table with
   exactly FOUR columns: `Result`, `Oracle complexity`, `Novelty`, `Limitations`.
   Bold the column headers. Separate every pair of data rows with `\midrule`;
   use a single thick `\midrule[1.2pt]` between the last of our rows and the
   first prior-work row. Keep the other row separators at the default thickness.
   Do not add assumptions, required-input, output or method-description columns.
   Put material differences in assumptions, tuning knowledge, oracle access, outputs
   and complexity in Novelty or Limitations, as short explicit comparisons.
   Shared setup assumptions remain below the caption; do not repeat them in cells.
   Use formulas and short, direct comparison sentences; avoid dense paragraphs.
   Leave Novelty and Limitations empty in our rows (no dashes or placeholder text). Populate
   these columns ONLY in prior-work rows, always from our results' perspective:
   Novelty states what ours improves over that baseline; Limitations states
   what ours loses (e.g. worse noise dependence or stronger assumptions).
   Lead Novelty with our strongest supported result against that row, including
   its validity regime and a quantitative gain where available. A limitation
   must not erase a supported gain. Ensure the review's substantive contribution
   is visible in the comparisons, not only in the star rating; do not invent
   improvements to justify that rating.
   If prior work also guarantees a stronger output, still state a supported cost
   saving for the shared target in Novelty, with its regime; put the lost extra
   guarantee in Limitations. Do not present this as a speedup for identical outputs.
   Keep conditions attached to their claims. Do not invent disadvantages for
   symmetry: leave the cell empty if none is established. Do not fill it with
   "No additional restriction identified" or generic caveats. A deterioration
   outside the comparison method's admissible range is not a comparative loss.
   A matched rate belongs in Novelty, not Limitations. Do not put unresolved
   priority, novelty, or optimality in Limitations: those are not losses against
   the numbered comparison method. Preserve a supported worse leading constant
   as a short prose limitation even though big-O hides it. State a comparative requirement
   tradeoff directly, e.g. `needs $R,\Delta$ in addition` in Limitations.
   Give only gains supported by the review. Prefer short connected sentences;
   use numbered items only when they make several distinct gains easier to read. Aim for at most 30 prose words per cell, excluding formulas
   and citations; keep a necessary validity condition even if it needs more.
   Preserve useful quantitative examples from the reviews: state the parameter
   regime and compare total big-O bounds when this makes a gain concrete. Do not
   replace such an example with a vague claim of improvement merely to meet the
   word budget. Use a line break between numbered items. Cut secondary method descriptions
   and repeated qualifications before exceeding this budget.
   State the change directly: e.g. `$x$ instead of $x^2$`, `no bounded-gradient
   assumption`, `no knowledge of $L$`, or `last iterate instead of averaging`.
   These are examples of wording, not claims to copy. The baseline is already
   identified by its row; do not repeat its citation in the comparison cells.
   Refer to all results by their table-local numbers: `(1): ...`, `(2): ...`,
   or `(1), (2): ...` for a shared gain. Use explicit row numbers instead of "the baseline" or a method-name substitute
   in comparison cells. Repeat the target number only when needed for clarity.
   Do not write `both`, `first`, `second`,
   `next row`, or descriptive substitutes. State each supported improvement in
   parameter dependence as well as oracle access; do not reduce a rate improvement
   to merely removing a search. Distinguish a matched rate from a strict gain,
   and give conditions for gains in individual terms without implying total-cost
   dominance. Do not imply every one of our results has the same gain.
   Mention last iterate versus average ONLY when it is a supported contribution
   or changes the validity of the comparison; otherwise omit output descriptions.
   If no improvement is supported, say `Matches known rate` or `No established
   improvement`, as appropriate. Do not invent a gain to fill the cell.
   Retain the conditions for a claimed gain and essential baseline validity
   restrictions in the relevant comparison cell. Do not hide restrictions in
   Abbr, omit tradeoffs, or imply identical assumptions.
2. Place the caption first, followed immediately by a concise paragraph of shared
   assumptions and the accuracy target, then the table. Link the exact setup file
   in the caption. Place the caption and assumptions OUTSIDE threeparttable,
   before opening it: otherwise its delayed caption can reverse their order.
   State only the setup's actual hypotheses: do not silently add completeness,
   finite dimension, or stronger smoothness just to use a familiar description.
3. Number EVERY result row `(1)`, `(2)`, ... in display order, restarting in each
   table. Number our rows first, then continue numbering through prior-work rows.
   Never restart numbering at the prior-work separator.
   Use bold numbers `\textbf{(1)}`, `\textbf{(2)}`, ... both in result labels
   and in Novelty and Limitations references. For our rows, place the number before the exact theorem
   basename, hyperlinked to the supplied
   `LongTails/Theorems/<basename>.lean` URL and a bold `(Ours)` label.
   Add a short `\href{<supplied review_url>}{(review)}` link only in each of our result rows.
   Replace textual verdicts with stars in parentheses beside each of our method labels:
   SUBSTANTIVE NOVELTY SUPPORTED = `$(\star\star\star)$`;
   LIMITED OR INCREMENTAL NOVELTY = `$(\star\star)$`;
   INCONCLUSIVE (or missing verdict) = `$(\star)$`;
   ALREADY KNOWN OR STANDARD COROLLARY and NO IMPROVEMENT = no stars.
   Rate each method separately, applying the negative-example corrections;
   do not give every method the setup's maximum score. Do not rate prior methods.
   Do not spell out verdicts or add significance commentary in comparison cells.
   Do not substitute an invented descriptive method name. Allow breaks between
   CamelCase words without changing the visible name. These are our theorem
   statements; the label does not assert invention of a classical algorithm.
4. Prefix each prior-work result label with its bold row number, then identify
   prior work with `\citep{key}`. A standard method name may precede it,
   but do not manually repeat author names next to the citation. Retain a version
   or theorem locator only if necessary to identify the guarantee being compared.
   Do not add review links to prior-method rows; use their paper citations only.
5. Below the table put `\textbf{Abbr:}` followed only by symbol definitions and
   conventions needed to read the formulas. Prefer explicit dependence on the
   setup parameters. Introduce abbreviations such as $A,B,S,T$ sparingly, only
   when a long or repeated expression would otherwise be unwieldy; do not hide
   a readable rate behind placeholders merely to keep it on one line. Define
   any necessary abbreviation explicitly in the setup parameters. Use standard
   mathematical notation, including `\nabla^2 f` for the Hessian.
6. Use short, direct statements of contributions and limitations in the rows.
   List only material limitations affecting applicability, complexity, or
   implementation; omit routine technical distinctions unless their consequence
   is substantial.
   Remove repeated prose and generic disclaimers. Do not add comments about
   excluded setup files, zero-call cases, the generation process, or routine
   algorithm properties such as absence of restarts unless they distinguish a
   material contribution. Do not append an editorial essay to `Abbr:`.
   This is a factual comparison, not a review of the reviews. Avoid phrases such
   as "Review's composition is not a directly stated theorem", "routine adaptation",
   or "limited novelty". For a supported derived baseline, label it `Derived bound`
   and state its actual assumptions and costs. If a bound cannot be supported,
   omit that bound rather than filling a cell with review-process commentary.
7. No red highlighting, color legends, reviewer-confidence labels,
   source comments, or other LaTeX comments. Hyperlinks may use the paper's style.
   Preserve substantive qualifications in the relevant row instead of replacing
   them with a generic warning that assumptions might differ.

FORMAT

Produce a complete `table` environment, not a document. Packages available:
amsmath, amssymb, array, booktabs, tabularx, threeparttable, textcomp, natbib,
hyperref. The table must work with numeric natbib (`\usepackage[numbers]{natbib}`),
`\input{results_table.tex}`, `\clearpage`, `\bibliographystyle{plain}` and
`\bibliography{results_table}`. Do not require an author-year bibliography style.
The host document uses `changepage` to wrap every `table` in
`\begin{adjustwidth}{-2.5cm}{-2.5cm}`: tables extend equally into both side margins.
Use this wider available width when choosing formula breaks and page layout;
do not add another margin adjustment inside the generated tables.
Use `\linewidth` and `\footnotesize` for cells and the setup paragraph/abbreviations.
Do not scale or rotate the table or define macros. Keep formulas on one line
whenever they fit their column; avoid unnecessary forced line breaks. Break only
formulas that would overflow, rather than shrinking the font.
Use this four-column layout (adjust widths if needed):

\begin{table}[tp]
\centering
\caption{...}\label{tab:<exact-setup-basename>}
\parbox{\linewidth}{\footnotesize ...shared assumptions and target...}\par\smallskip
\begin{threeparttable}
\footnotesize
\setlength{\tabcolsep}{4pt}\renewcommand{\arraystretch}{1.25}
\begin{tabularx}{\linewidth}{@{}>{\raggedright\arraybackslash}p{0.20\linewidth}>{\raggedright\arraybackslash}p{0.32\linewidth}>{\raggedright\arraybackslash}p{0.25\linewidth}>{\raggedright\arraybackslash}X@{}}
\toprule
\textbf{Result} & \textbf{Oracle complexity} & \textbf{Novelty} & \textbf{Limitations} \\
\midrule
...our row, with bold number... \\
\midrule
...next row... \\
\midrule[1.2pt]
...prior-work rows... \\
\bottomrule
\end{tabularx}
\begin{tablenotes}[flushleft]\footnotesize
\item[] \textbf{Abbr:} ...definitions only...
\end{tablenotes}
\end{threeparttable}
\end{table}

Keep exactly these four columns for every setup. Keep the table compact while
retaining every material contribution and validity condition. No enforced total
page budget. Do not compile in this per-setup session or claim a page-fit check.

OUTPUT CONTRACT

Write only the JSON file at the supplied destination, with exactly these fields:

- `contribution`: map each supplied review's final verdict without reassessing it:
  SUBSTANTIVE NOVELTY SUPPORTED = 3; LIMITED OR INCREMENTAL NOVELTY = 2;
  INCONCLUSIVE = 1; ALREADY KNOWN OR STANDARD COROLLARY or NO IMPROVEMENT = 0. Use the maximum
  across this setup's theorems. If a review has no clear verdict, use 1 for it.
  The numeric score is sorting metadata; show only each method's stars, never
  the numeric score or textual verdict, in the visible table.
  Contribution type does not itself determine the score.
- `theorems`: list of the supplied theorem basenames, each exactly once.
- `table`: complete LaTeX table as specified above, ending with `\end{table}`
  after `\end{threeparttable}`. Escape JSON backslashes once.
- `bibliography`: map of NEW citation keys to complete BibTeX entry strings.
  In printed fields such as `note`, wrap URLs in `\url{...}` and escape LaTeX
  special characters in ordinary text; entries must compile with `plain.bst`.
  Verify each cited reference against its official publisher/proceedings page,
  DOI record, or arXiv record. Include the full article title and full author list;
  check year, venue, DOI/arXiv identifier, URL, and cited version. Prefer official
  BibTeX exports. Do not mix metadata or theorem numbering from different versions.
  Check that each cited theorem/section exists in that version and supports the
  guarantee attributed to it; inspect its statement and assumptions, not just the
  abstract. Omit an unsupported bound if the source is mismatched or inaccessible;
  do not replace it with verification-process commentary in the table.
  Do not invent missing metadata. Use `@misc` with the verified identifier/URL
  when publication details are unavailable. Reuse a snapshot entry only when it
  is correct and complete; otherwise emit a corrected entry under a new key and
  cite that key. Cite only references used in this table.

Parallel sessions generate other setups. Do not modify the existing table or
bibliography, source files, or another session's output. The runner merges and
sorts tables. Check before saving: exact theorem coverage; assumptions below
caption; notation below table; explicit extra assumptions where needed; consistent
four-column headers; advantages/disadvantages only in prior-work rows; brief explicit comparisons; valid links/citations; faithful formulas; no redundant commentary.
