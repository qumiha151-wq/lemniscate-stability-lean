# Two double points on the primitive rotating profile

In the centered coordinates of the [primitive rotating expander](PrimitiveRotatingProfile.md), the initial curve has two transverse double points in a least period. Each has two preimages in the parameter circle. The horizontal coordinates lie in the disjoint intervals $(6,6.2)$ and $(5.5,5.8)$. The absolute determinant of the two unit tangents exceeds $1/4$ at each crossing. A rotation, a positive dilation and a diffeomorphic change of parameter preserve this count, so every time slice of the physical solution has the same two double points.

## Locating the two pairs

Write $h$ for the verified positive arclength step and $v=s/h$ for the grid parameter. The two pairs belong respectively to
$
[1807,1815]\times[2204,2212],\qquad [1684,1692]\times[2395,2403].
$
The positions and tangents here come from the original differential equation. On each rectangle a nonsingular linear transformation of the difference of the two positions changes sign between the opposite faces in both coordinates. The rectangle intermediate value theorem gives a crossing. On the entire rectangle the absolute sine of the difference of tangent angles exceeds $1/4$. [Existence](../../../SolitonClassification/Rotating/IntegerChartIntersection.lean) · [Tangent bounds](../../../SolitonClassification/Rotating/IntegerCrossingTransverse.lean)

If two different parameter pairs in one rectangle yielded intersections, the corresponding two chords of the branches would agree. Project onto the direction perpendicular to this chord and apply Rolle's theorem on the first branch. Project the second branch perpendicular to the tangent found on the first branch, and apply Rolle's theorem again. The two tangents would be parallel, contradicting the bound on the sine. If one pair of parameters on a single branch coincides, the remaining branch has a zero chord and a single application of Rolle's theorem gives the same contradiction. Each rectangle therefore contains just one ordered pair. [Uniqueness](../../../SolitonClassification/Rotating/IntegerUniqueTransverseCharts.lean)

## Covering the rest of the period

The half-period $T$ satisfies $|T-4000h|\le10^{-30}$. The signed parameter range $[-4001,4001]$ contains the entire period. For ordered parameter pairs, recursively divide the rectangle into two rectangles along a coordinate, or divide an ordered square at its midpoint into two ordered squares and the rectangle between them. Children include their common edges.

* A pair at grid distance at most 32, or at least 7970, is either the same parameter modulo the period or has a short arc of length less than $0.3$ joining it. The absolute curvature on the whole profile is at most 10. Projection of that short arc onto its midpoint tangent is strictly increasing because the tangent angle changes by at most $10(0.3)/2<\pi/2$ from the midpoint. Distinct parameters on the short arc have different positions.
* Each reference position is enclosed within $10^{-4}$ in both coordinates. Since the arc has unit speed and $h<7553\times10^{-6}$, one coordinate interval about each reference covers its entire parameter interval. Disjoint coordinate intervals exclude a crossing. There are 1,872 such rectangle leaves.
* Forty-two pairs of adjacent grid intervals use projections onto explicit integer directions. Between two adjacent reference points a projected arc differs from the linear interpolation of its endpoint projections by at most $10(|n_x|+|n_y|)h^2/8$. This follows from the second derivative bound applied to the sum and the difference with a quadratic. The calculation reserves $600\times10^{-6}$ per coordinate for this error, in addition to the endpoint uncertainty. In each of these pairs the enlarged projection intervals are disjoint.
* The remaining nine leaves lie inside one of the two crossing rectangles. The 512 short-arc leaves use the first argument above. This covers every ordered pair, including a pair meeting the seam. Restricting the arclength labels to the half-open period removes the duplicate label at its ends.

The finite certificate uses 1,146 signed reference nodes from the two certified shooting arms. The [subdivision verifier](../../../SolitonClassification/Rotating/IntegerGlobalLedger.lean) computes its inequalities on integers. The [rational replay](global_crossing_ledger.py) regenerates its reference table and decision tree alongside the two signed grids, `plus4000.jsonl.gz` and `minus4000.jsonl.gz`. The Lean proof uses the integer node values included in the project and checks each reference enclosure against the original signed arm. [Original signed grid construction](whole_tape.py) · [Reference position theorem](../../../SolitonClassification/Rotating/IntegerGlobalNodeTable.lean)

The [end-to-end theorem](../../../SolitonClassification/Rotating/IntegerFinalDoublePoints.lean) gives the pure-normal physical evolution, the initial crossing angles, and exactly two ordered pairs of distinct material parameters per least period on every physical slice. [Complete parameter-pair coverage](../../../SolitonClassification/Rotating/IntegerGlobalPairExclusion.lean) · [Preservation under physical time evolution](../../../SolitonClassification/Rotating/IntegerPhysicalDoublePoints.lean)

