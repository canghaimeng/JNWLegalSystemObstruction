# JNW Legal-System Obstruction

This Lean 4 project formalizes the explicit 33-vertex solution of the
non-parenthetical, four-connected form of Jankiewicz--Norin--Wise Problem 5.2.
It deliberately makes no claim about the stronger parenthetical condition on
all three-connected ordinary subgraphs.

## Build and reproduce

The project is pinned to Lean/Mathlib `v4.33.0`.

```bash
cd /home/box/Document/Math_era/math-research-lab/formal/JNWLegalSystemObstruction
lake update
lake build
rg -n --glob '*.lean' '\b(sorry|admit|axiom|unsafe)\b' .
```

The final scan is expected to print no source occurrence.  Generated `.lake/`
dependencies are outside that source scan.

## Theorem map

| Paper component | Lean module | Principal declaration |
| --- | --- | --- |
| JNW states, moves, affine orbits, legal systems | `JNWLegalSystem/Basic.lean` | `JNW.LegalSystem` |
| Legal systems force nonnegative two-curvature | `JNWLegalSystem/Averaging.lean` | `JNW.legalSystem_curvature_obstruction` |
| Hexagonal prism has negative two-curvature | `JNWLegalSystem/Seed.lean` | `JNW.Vertex.prism_noLegalSystem` |
| Exact induced-`C4` amalgam restriction | `JNWLegalSystem/Amalgam.lean` | `JNW.ExactC4Split.legalSystem_restrict_left`, `legalSystem_restrict_right` |
| Three concrete cap restrictions | `JNWLegalSystem/Stages.lean` | `JNW.Vertex.graph_noLegalSystem` |
| Explicit 33-vertex graph | `JNWLegalSystem/Construction.lean` | `JNW.Vertex.graph` |
| Four-connectivity certificate and standard lift | `JNWLegalSystem/Connectivity.lean` | `JNW.Vertex.fourVertexConnected` |
| Ordinary-subgraph collapse | `JNWLegalSystem/Collapse.lean` | `JNW.ordinaryFourConnected_collapse` |
| Zero-parameter headline | `JNWLegalSystem/Main.lean` | `JNW.Vertex.jnw_problem5_2_four_connected` |

## Structural proofs versus finite computation

The general mathematics is proved structurally: the orbit averaging theorem,
the singleton obstruction, the exact `C4` restriction, the restriction of
coefficients to a shore, and the ordinary-subgraph collapse do not use a
finite search oracle.

The explicit host gates use kernel-checked finite computation where this is
most transparent.  `native_decide` checks the vertex and edge counts,
4-regularity, triangle-freeness, the displayed four-cycle, each concrete cap
interface, and the finite BFS certificate for all 6,018 vertex-deletion sets
of size at most three.  `Connectivity.lean` proves structurally that membership
in the computed BFS closure yields a Mathlib walk and hence converts the finite
certificate into the standard `SimpleGraph.Connected` deletion statement.

The headline theorem packages both forms of evidence.  It states that the
explicit graph has 33 vertices and 66 edges, is 4-regular and four-vertex-
connected, has no triangle and has girth at least four (indeed it contains the
displayed interface four-cycle), has two-curvature one, admits no JNW legal
system, and has no proper four-connected ordinary subgraph.

