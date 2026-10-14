# Wiki publishing and maintenance

The canonical maintained wiki lives in the repository's `docs/wiki/`
directory, not in a manually edited copy. The GitHub Wiki tab uses
a separate `.wiki.git` Git repository, so a committed Markdown page
is **not** proof that the live Wiki page already exists.

[.github/workflows/publish-wiki.yml](../../.github/workflows/publish-wiki.yml)
follows the established `lean-milliken` mechanism: pushes that change
`docs/wiki/**` on main trigger synchronization by
`Andrew-Chen-Wang/github-wiki-action@v5` after verifying that
the separate Wiki Git repository is initialized. An initial
`gollum` event and a manual `workflow_dispatch` can also start it.
The version-controlled `docs/wiki/README.md` becomes Wiki Home,
and `_Sidebar.md` supplies navigation. The publisher does not
force-push Wiki history.

## One-time Wiki initialization, if needed

1. Visit https://github.com/janhubicka/lean-all-those-ramsey-classes/wiki
   while logged into an account with Wiki edit rights.
2. If GitHub presents **Create the first page**, create **Home**
   and save any initial sentence. This initializes
   `lean-all-those-ramsey-classes.wiki.git`.
3. The Wiki edit should trigger publishing automatically; use the
   [publishing workflow](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/workflows/publish-wiki.yml)
   to run it manually if required.

Until that Git repository exists, the workflow explicitly reports
an initialization notice rather than pretending pages were published.
The [source-controlled index](README.md) is always readable.

## Ongoing formalization updates

After **full GitHub Actions and axiom-audit success** for a new proof,
update the corresponding public API (only for genuinely proved
endpoints), `CheckAxioms*.lean`, root README and the relevant wiki
theorem/application status. When it formalizes a paper statement,
update its nonprinting manuscript validation marker and TODO entry
while preserving the paper's reversible correction provenance.
Do not label a conditional application or a component as a
Ramsey-class theorem.

Update source pages in pull requests; the workflow publishes
merged changes automatically. The Wiki is documentation, not a
substitute for inspected Lean theorem statements or kernel checks.
