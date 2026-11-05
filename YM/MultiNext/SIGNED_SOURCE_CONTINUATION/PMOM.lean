import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Routes

set_option warningAsError false

/-!
#  PMOM.1. Polynomial moments of actual real log-link tensors

and correction for degenerate torus

This doesn't assert the Gaussian/operator estimates using them.

Connection
needed thru physical `P=H.p` masks in `Hearts`: those from `C` are on periodic
link arrays.

Here use **those** degrees and projection tests, d from available
Smooth, no complexification assumed.

Doing this at the unmasked regular function, not differentiating the
indicator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Mom
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open Powers Mediator Next.Foundations Pattern Broadcast
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {d m b : ℕ} {n : Side} (o : Site n) (X : Support n)

def screen : Directions G n →L[ℝ] Directions G n :=
  ContinuousLinearMap.pi fun i => if needed X i then ContinuousLinearMap.proj i else 0
lemma screen_at (p : Directions G n) (i) : screen X p i = if needed X i then p i else 0 := by
  unfold screen; simp; split <;> rfl

/-- Entire-summand PMOM in the intended periods, restricted
at actual LocalOn X. `Maps` tests bounded ordinary degree; use
`Powers.positions` to apply to literal positioned link arrays (monomials
on E4, cover convention, apply then evaluate on the native lift).
Supports for the link variations themselves needn't be X: pass the
`screen` field whose values are used by the stencil.
The grade b can be lower than Snap's d (to use for E submissions asking
only lower moments of a nontrivial label). -/
lemma wiped {u : Config G n → ℂ} (H : Hol G) (h : LocalOn X u) (hw : GaugeInvariant u) (hX : Nonwrapping X o)
    (hn : 2 ≤ n.val) (hb : b ≤ d) (hp : ContDiffAt ℝ b (u ∘ increment 1) 0)
    (he : ∀ J : Jet G,∀ k,k ≤ b → iteratedDeriv k (fun t => u (H.testLinks d o J t)) 0=0)
    (p : Fin m → ℕ) (w : Fin m → Directions G n)
    (ht : ∑ i,p i ≤ b) (hP : ∀ i,1 ≤ p i ∧ screen X (w i)∈Maps o X (p i)) :
    iteratedFDeriv ℝ m (fun v => u (increment 1 v)) 0 w=0 := by
  let A (k : ℕ) := (Sites o X k (G:=G) (d:=d):Set (Slate G n d))
  let K i := (Maps o X i (G:=G) : Set (Directions G n))
  let Q := u ∘ increment 1
  have hZ : Q=Q ∘ screen (G:=G) X := by
    funext v; apply h; intro i ha hh
    change G.lieExp _*_ = G.lieExp (screen X v i)*_
    rw [screen_at, if_pos (show needed X i from ⟨ha,hh⟩)]
  obtain ⟨hD,h₀⟩:= osmotic (G:=G) (d:=d) X o
  have hz := attenuation A K (optic X o) Q (hD.of_le le_top) h₀ hp (fun i hi hk => covers o X hX hn i hi (hk.trans hb))
    (along o X hn hX) (formal_null (o:=o) (X:=X) d H h hw he hp)
  have hM : m ≤ b := le_trans (by simpa using sum_le_sum (s:=Finset.univ) (f:=fun _ => 1) (fun i _ => (hP i).1)) ht
  change iteratedFDeriv ℝ m Q 0 w=0; nth_rw 1 [hZ]; rw [jets_linear (screen X (G:=G)) (hp.of_le (Nat.cast_le.mpr hM))]
  exact hz m p (fun i => screen X (w i)) ⟨fun i => hP i,ht⟩



/-- Real derivatives of the h-weighted pure-degree read. -/
lemma label_reads {z : Label G d} {x y : ℕ} (hz : z∈Grade (x,y)) (J : Jet G) (i : ℕ) (h : i<x) :
    iteratedDeriv i (fun t => read (scaleJet J t) z.val) 0=0 := by
  rw [deriv_read]
  have ht : MvPolynomial.IsWeightedHomogeneous generation z.val x := by
    intro j he; exact congrArg Prod.fst ((Labels.weight_slot j).symm.trans ((pure_grade _ _).mp hz he))
  rw [tier,ht.weightedHomogeneousComponent_ne _ h.ne,map_zero,smul_zero]


end YM.MultiNext.SignedSource.Mom
