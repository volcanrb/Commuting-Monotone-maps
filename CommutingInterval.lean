import CommutingInterval.PiecewiseMonotoneMain
import CommutingInterval.Eigenmeasure

/-!
# Common fixed points for weak finite-piece monotone interval maps

This is the public entrypoint for the theorem that two commuting continuous
self-maps of `[0,1]`, weakly monotone on the cells of finite partitions, have
a common fixed point.  The proof passes through the unconditional
piecewise-linear theorem. The Eigenmeasure module relates the signed measures
of the transfer operator to their continuous cumulative functions.
-/
