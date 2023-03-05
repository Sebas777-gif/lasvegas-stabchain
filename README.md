# lasvegas_stabchain

The goal of this project is to implement and evaluate a Las Vegas algorithm for stabilizer chain computation for permutation groups in GAP.

The steps are the following (as described in [_Notes on Computational Group Theory_, Hulpke 2010](https://www.math.colostate.edu/~hulpke/CGT/cgtnotes.pdf)):

1. Compute a randomized stabilizer chain for $G$.
2. Using this chain, compute a composition series.
3. Using constructive recognition of the simple factors, write down a presentation for each simple factor.
4. Using the extension structure, construct a presentation for $G$. If the initial chain was too small this is in fact a presentation for a smaller group.
5. Verify that the elements of $G$ actually fulfill this presentation.