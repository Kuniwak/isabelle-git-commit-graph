Formal Definition of the Git Commit‑Graph Model
===============================================

This document gives a formally defined state‑transition model of a Git commit‑object graph that can be mechanically verified in Isabelle.
With this definition, you can quickly write formal definitions of Git branching strategies and formal specifications of the tools that surround them.

To keep the focus on describing the commit graph itself, the concepts of tree and blob objects are omitted.
Consequently, this model is not suitable for formally specifying tools—such as merge drivers—that manipulate trees or blobs.
Moreover, because orphan branches are rarely used, we assume that any two commits in the graph share a common ancestor.
This lets us ignore merge‑failure cases caused by the absence of a common ancestor.

An example definition of a branching strategy can be found in [`ExampleBranchStrategy.thy`](./ExampleBranchStrategy.thy).

⸻

Types

<dl>
<dt>Git State</dt>
<dd><code>(commit graph * commit)</code></dd>
<dt>Graph</dt>
<dd><code>('a set * 'a rel)</code></dd>
<dt>Commit</dt>
<dd>Abstracted as natural numbers, since only distinguishability between commits is required.</dd>
</dl>

The initial state of the system is provided by `init`.

Transition Functions

<dl>
<dt><code>merge</code></dt>
<dd><code>merge  :: git ⇒ commit set ⇒ git option</code></dd>
<dt><code>commit</code></dt>
<dd><code>commit :: git ⇒ commit     ⇒ git option</code></dd>
</dl>

License
-------

MIT License
