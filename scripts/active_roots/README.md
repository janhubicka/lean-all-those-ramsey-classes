# Active Lean proof roots

Each newly checked, independently supported Lean proof module that is not
already reachable from a public import root is registered by one `.txt` file
in this directory. Name the file after the final component of the fully
qualified Lean module name. Its single non-comment line is the exact module
name, for example:

```text
AllThoseRamseyClasses.Applications.MetricJumpSandwich
```

`scripts/cleanup_inventory.py --verify` rejects missing or malformed roots,
incorrect filenames, redundant roots already listed in the historical
`ACTIVE` set, orphan Lean modules, and stale axiom-audit files. It does not
delete files. The default and `--plan` options print the proposed cleanup.

New PRs should add their own marker rather than editing the shared historical
`ACTIVE` set. Independent features then do not contend over the same
inventory file during GitHub squash merges. If a feature is retired, delete its marker and demonstrably unused source
in the same reviewed cleanup PR; Git history preserves earlier experiments.
A marker may also become **transitively redundant** when a newer protected
root imports its module. Remove the redundant marker alone in that case,
NEVER the imported Lean proof. Run `scripts/cleanup_inventory.py --plan`
for a witness ("REDUNDANT_MARKER ... via ..."). The repository still
compiles all Lean modules and audits their named theorems. No compatibility
wrappers are required.

Existing roots may remain in the historical static set; they need not be
mass-migrated merely to use this mechanism. The
`MetricJumpSandwich.txt` marker exercises the new mechanism in CI while
preserving exactly the same active imports as before this change.
