# A Cost Analysis Framework in Lean

This repo aims to provide a framework for cost annotation and analysis of algorithms written in Lean. It is based off of [agda-calf](https://github.com/HarrisonGrodin/agda-calf), a cost-aware logical framework implemented in Agda.

We want a practical framework for analyzing the cost of algorithms and cryptographic reductions in Lean (which includes, among other things, integrating cost analysis with effectful computations that may make oracle access).

## References

- [A Cost-Aware Logical Framework](https://dl.acm.org/doi/10.1145/3498670), by Yue Niu, Jonathan Sterling, Harrison Grodin, and Robert Harper (POPL 2024)
- [Decalf: A Directed, Effectful Cost-Aware Logical Framework](https://dl.acm.org/doi/10.1145/3632852), by Harrison Grodin, Yue Niu, Jonathan Sterling, and Robert Harper (POPL 2025)
- [Polynomial Time and Dependent Types](https://dl.acm.org/doi/10.1145/3632918), by Robert Atkey (POPL 2024)
- [A Formalization of Polytime Functions](https://link.springer.com/chapter/10.1007/978-3-642-22863-6_11), by Sylvain Heraud & David Nowak (ITP 2011)
- [Linear types and non-size-increasing polynomial time computation](https://ieeexplore.ieee.org/document/782641), by Martin Hoffmann (LICS'99)
- [A New Recursion-Theoretic Characterization of the Polytime Functions](https://dl.acm.org/doi/abs/10.1145/129712.129740), by Stephen Bellantoni and Stephen Cook (STOC'92)