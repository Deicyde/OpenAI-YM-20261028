import YM.Planned.PRIMARY_INTEGRAL_295.Bigrade
import YM.Planned.PRIMARY_INTEGRAL_295.Cases
import YM.Planned.PRIMARY_INTEGRAL_295.Spot


/-!
# Flat cancellation in engineering degree

If a whole cylinder's h-jet vanishes up to the given degree, its entire
logarithmic chart annihilates lists of polynomial link directions there,
including lower polynomial orders about the same anchor.

This is not
assuming a leading response.

Need gauge invariance and all words and paths
of the cylinder on its stencil; the derivative tested here is *before* any
indicator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Place
open Function Filter Lattice Labels Source Source.Drops RG Wilson WardBin MeasureTheory Next.Foundations
open scoped BigOperators ContDiff Topology Matrix.Norms.Frobenius
variable {G : Gauge} {d n q : ℕ} {S : Finset Cover}

section Germ
variable {f : CoverConfig G → ℂ} (hx : LocalOn S f) (hy : GaugeInvariant f) (H : Hol G)

include hx hy H
private lemma lit_snap (hf : ContDiffAt ℝ d (f ∘ pore (S:=S)) 0) :
    ContDiffAt ℝ d (f ∘ pureQuest H (d:=d)) 0 := by
  let I := ContinuousLinearMap.inr ℝ (S → G.Color) (Snap G d)
  have he : Tendsto I (𝓝 0) (𝓝 0) := by simpa only [map_zero] using I.continuous.tendsto 0
  let F := opened S (G:=G) (d:=d) ∘ I
  have hF : ContDiffAt ℝ d F 0 :=
    (show ContDiffAt ℝ d (opened S (G:=G) (d:=d)) (I 0) by rw [map_zero]; exact (opened_smooth S G d).of_le le_top).comp _
      I.contDiff.contDiffAt
  have hf0 : F 0=0 := by simp [F]
  apply ((hf0.symm ▸ hf).comp (f:=F) (0:Snap G d) hF).congr_of_eventuallyEq
  filter_upwards [he.eventually (lit S hx hy H d)] with v hv; exact hv.symm

private lemma snaps (hf : ContDiffAt ℝ d (f ∘ pore (S:=S)) 0)
    (hl : ∀ J k, k < q → leading k (fun t => f (H.links d J t))=0)
    (hd : q ≤ d+1) (X : Fin n → Snap G d) (w : Fin n → ℕ) (hw : ∀ i, throughSlot (X i) (w i))
    (hk : n≤d) (h : ∑ i,w i < q) : iteratedFDeriv ℝ n (f ∘ pureQuest H) 0 X=0 := by
  classical
  let u (i : Fin n) (j : Fin (d-1)) : Snap G d := Pi.single j (X i j)
  have he (v : Jet G) (k : ℕ) (h : k < q) :
      leading k (fun t => (f ∘ pureQuest H) (engineered t (trunk d v)))=0 := by
    rw [show (fun t => (f ∘ pureQuest H) (engineered t (trunk d v))) = fun t => f (H.links d v t) from
      funext fun t => congr_arg f (scales H v t).symm]
    exact hl v k h
  rw [show X=(fun i => ∑ j,u i j) from funext fun _ => (Finset.univ_sum_single _).symm]
  rw [ContinuousMultilinearMap.map_sum _ u]; refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hP : ∀ i,(p i).val+2 ≤ w i
  · have hv : Parts.rate p ≤ ∑ i,w i := Finset.sum_le_sum (fun i _ => hP i)
    have ha := hv.trans_lt h
    exact Parts.no_derivative (lit_snap hx hy H hf) hk p (by omega) (fun J => he J _ ha) (fun i => X i _)
  push Not at hP; obtain ⟨i,hi⟩ := hP
  refine ContinuousMultilinearMap.map_coord_zero _ i ?_
  unfold u; simp only [hw i (p i) hi, Pi.single_zero]

set_option maxHeartbeats 900000 in
/-- All-positive weights; arity induction removes only terms where the
number of *outer* derivatives strictly decreased. -/
private lemma cancellation_positive (hf : ContDiffAt ℝ d (f ∘ pore (S:=S)) 0)
    (hl : ∀ J k, k < q → leading k (fun t => f (H.links d J t))=0) (hd : q ≤ d+1) :
    ∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0<w i) → (∑ i,w i)<q → ∀ u : Fin n → Potential G,
    (∀ i,u i ∈ rangeLt (Axis→G.Color) (w i)) →
      iteratedFDeriv ℝ n (f ∘ pore (S:=S)) 0 (fun i => ping S (u i))=0 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hw hW u hu
    have hl' : ∑ i,w i ≤ d := by omega
    have hk : n≤d := (Cases.arity hw).trans hl'
    have hb (i : Fin n) : w i ≤ d := (Finset.single_le_sum (f:=w) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)).trans hl'
    choose v X hv hX h using fun i => generated (u i) (hu i) (hb i)
    let V (i : Fin n) := expandCode S (v i) (X i)
    let W := f ∘ pore (S:=S)
    let g : EntryCode S G d → Dev S G := opened S
    have hm : W ∘ g =ᶠ[𝓝 0] ((f ∘ pureQuest H) ∘ Prod.snd) := lit S hx hy H d
    have hz : g 0=0 := opened_zero _
    have ht : ContDiffAt ℝ d g 0 := (opened_smooth ..).of_le le_top
    have he : iteratedFDeriv ℝ n (W ∘ g) 0 V=0 := by
      let Z := ContinuousLinearMap.snd ℝ (S → G.Color) (Snap G d)
      have hf' : ContDiffAt ℝ n (f ∘ pureQuest H (d:=d)) 0 := (lit_snap hx hy H hf).of_le (Nat.cast_le.mpr hk)
      have Hq := jets_linear Z hf'
      calc
        _ = iteratedFDeriv ℝ n ((f ∘ pureQuest H) ∘ ⇑Z) 0 V := DFunLike.congr_fun (show iteratedFDeriv ℝ n (W ∘ g) (0:EntryCode S G d) = _ from (hm.iteratedFDeriv ℝ n).eq_of_nhds) V
        _ = _ := (DFunLike.congr_fun Hq V).trans (snaps hx hy H hf hl hd X w hX hk hW)
    have h1 (c : OrderedFinpartition n) (hc : c ≠ .atomic n) : Cases.caseRead c W g 0 V=0 := by
      have hlen : c.length < n := lt_of_le_of_ne c.length_le (fun hl => hc (Cases.finest c hl))
      let β := Cases.costs c w
      have h2 (i : Fin c.length) : ∃ f : Potential G,f∈rangeLt (Axis→G.Color) (β i) ∧ ping S f=
          iteratedFDeriv ℝ (c.partSize i) g 0 (V ∘ c.emb i) :=
        opened_audits S (v ∘ c.emb i) (X ∘ c.emb i) (w ∘ c.emb i) (fun s => hw _) (fun s => hv _) (fun s => hX _)
      choose U hU hh using h2
      have he : ∑ i,β i < q := (Cases.all c w).trans_lt hW
      unfold Cases.caseRead; rw [hz,show (fun i => iteratedFDeriv ℝ _ g 0 (V ∘ c.emb i)) = (fun i => ping S (U i)) from (funext hh).symm]
      exact ih _ hlen β (Cases.live c hw) he U hU
    rw [Cases.compReads (hz.symm ▸ hf) ht (Nat.cast_le.mpr hk) V, Finset.sum_eq_single (.atomic n),Cases.one,hz] at he
    · have hx (i) : fderiv ℝ g 0 (V i)=ping S (u i) := by rw [show fderiv ℝ g 0 (V i) = _ from opened_launch (v i) (X i),← h]
      simp_rw [hx] at he; exact he
    · exact fun i _ he => h1 i he
    simp

/-- This is the actual H flow.

Does not
require analytic f.

All grades and all log-link directions in the tested
polynomial spaces (no use of phase characters), including arity zero
and all degenerate zero-weight inputs.

Assumes d chosen for which these
jets exist.

The *placement* application uses non-wrapping supports. -/
theorem cancellation (hf : ContDiffAt ℝ d (f ∘ pore (S:=S)) 0)
    (hl : ∀ J k, k < q → leading k (fun t => f (H.links d J t))=0) (hd : q ≤ d+1)
    (w : Fin n → ℕ) (h : ∑ i,w i < q) (u : Fin n → Potential G) (hu : ∀ i,u i ∈ rangeLt (Axis→G.Color) (w i)) :
      iteratedFDeriv ℝ n (f ∘ pore (S:=S)) 0 (fun i => ping S (u i))=0 := by
  classical
  by_cases hv : ∀ i,0 < w i
  · exact cancellation_positive hx hy H hf hl hd n w hv h u hu
  push Not at hv; obtain ⟨i,hi⟩ := hv
  have ht:=hu i; rw [show w i=0 from by omega, rangeLt, Submodule.mem_bot] at ht
  apply ContinuousMultilinearMap.map_coord_zero _ i; rw [ht,map_zero]
end Germ
end YM.Planned.PrimaryIntegral295.Place
