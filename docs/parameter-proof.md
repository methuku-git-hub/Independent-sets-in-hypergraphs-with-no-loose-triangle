# Checked parameter substitution

This sufficient parameter choice replaces the manuscript's optimized one.
It preserves the target theorem and its quantifier order. Every estimate below
is proved in `KMV.Parameters`, `KMV.SamplingParameters`, `KMV.ColorParameters`,
`KMV.AssemblyBounds`, `KMV.ReducedAssembly` and `KMV.Main`.

Let B = 8(18r + sum_{j=4}^r j(2r)^(j-2) + 1), l = log n,
Q = log log n, and t = n^(2/3) Q^(1/3). The structural reduction either gives
an independent set of size t or retains at least 7n/8 vertices, with
3-degree at most Bt, 4-degree at most Bn, triple codegree at most B, and
m_j at most n²(2r)^(j-2) for j ≥ 4.

| Quantity | Value |
|---|---|
| p | n^(-1/3) l^(1/100) |
| beta | n^(-3/10) |
| L3 | n^(1/3) l^(-1/2) |
| L4 | n^(2/3) l^(-1/2) |
| A | 10B n^(1/3) l^(1/2) Q^(1/3) |
| D3 | 128B l^(1/50) Q^(1/3) |
| D4 | 128B l^(3/100) |
| Coloring upper bound | 12800B l^(1/100) Q^(-1/3), before the Li–Postle constant C |

Natural ceilings supply the integer counting bounds. Once their real arguments
are at least 1, each ceiling is at most twice its argument. Edges containing an
auxiliary graph edge are filtered out for pair-codegree counting; on a sampled
graph-independent vertex set the original induced hypergraph is exactly the
same as the filtered one. The sampling law is restricted to the structural
survivor set, so isolated vertices outside it cannot inflate the retained size.

The exact normalized configuration loss is a finite sum of terms with negative
leading n exponents, or zero n exponent and negative log n exponent.
`loss_envelope_identity` proves the algebraic equality;
`normalizedLoss_tendsto` proves convergence to zero, including the sum over
all edge sizes 5 through r. Thus the configuration cost is eventually at most
pn/8. Random degree trimming costs at most 7pn/128, hence at most pn/16.

The entropy ratio converges to zero. The checked bound gives a sampling marginal
at least p/2. Starting with 7n/8 vertices therefore gives expected sample size
at least 7pn/16. Cleaning leaves at least pn/4 vertices with edges of size 3 or
4, no Li–Postle triangle, and degree bounds D3 and D4.

For Q ≥ 1, both D3 and D4 are at least 8, and log D_j ≥ Q/100. The two coloring
terms are bounded by 12800B l^(1/100) Q^(-1/3). Dividing the surviving-set size
by this bound and the assumed constant C gives the desired factor. The final
constant is min(1, 1/(4C·12800B)); all eventual thresholds are chosen after r
and before n and H. No numeric bound or limiting assertion remains a hypothesis
of `KMV.main_result`.
