import YM.RG08.Atlas.Church
/-! # Total exponent germ law -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Mount
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function
open Stationary Bloch Laurent Precision Line Finset Bid Work.F03 Matrix
open Tack Rudder Aggregate Symmetry Steam Cairn Cloud
open scoped BigOperators Classical ContDiff Topology Matrix Matrix.Norms.Frobenius NNReal InnerProductSpace PowerSeries
variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K:KernelChoices}{I J:Type}{n e:ℕ}{C:Castle G}

-- at any requested tap, restriction through that n is exact
lemma china_focus (h:S.patch.Branches S.kernel G)(t:S.Choices)(hh:Stable C){N k:ℕ}(hk:k ≤ N):
 tap k (china h C)=tap k (-((∑ i∈range (N+1),∑ r∈range (i+1), leaf S (C r i) (stick r) i)+tax 2 (flask (fair S t)))):=by
 rw [china_tap _ _ _ hh];unfold tap;rw [map_neg,map_add,map_sum];simp_rw [map_sum];congr 2
 apply sum_subset (by intro i hi;simp only [mem_range] at *;omega);intro i _ hi;apply Finset.sum_eq_zero;intro r hr
 rw [leaf,PowerSeries.coeff_X_pow_mul',if_neg (by simpa using hi)] -- etc

private lemma belt_finite {J I : Type} (a b : J → Port I) (F : ℕ → ℕ → Port J)
    (V H : Port J) (e : ℕ)
    (h : ∀ i ≤ e, tap i H = tap i (-((∑ i ∈ range (e + 1), ∑ r ∈ range (i + 1), F r i) + V)))
    (hf : ∀ r i, belt a (F r i) = belt b (F r i)) (hv : belt a V = belt b V) :
    tap e (belt a H) = tap e (belt b H) := by
  let T := -((∑ i ∈ range (e + 1), ∑ r ∈ range (i + 1), F r i) + V)
  have ht : belt a T = belt b T := by simp only [T, map_neg, map_add, map_sum, hf, hv]
  exact (steady_belt a e H T h).trans ((congrArg (tap e) ht).trans (steady_belt b e H T h).symm)

-- compare all output aggregate ingredients BEFORE Wick. inputs A,B change on internal and
-- external slots preserving same step's deterministic noise covariance & normalized hair
-- ratio. Here only field dependence consumed. Sym rotated & translated. Full transformation
-- of purges below through actual boiler.
lemma blossom (S:StepData c f)(h:S.patch.Branches S.kernel G)(hC:Stable C)[Fintype I](t:Signed)(u:Site c) :
 ∀ A B:Strip (Epic S.patch G _) I, (∀ i,Pace (A i))→(∀ i,Pace (B i))→ roll A 0=0→ roll B 0=0→
 (∀ᶠ z in 𝓝 0,∃ v:Site f→G.El,
    represent (low S (roll B z))=Lattice.gauge v (Lattice.pull t (S.ratio.embed u) (represent (low S (roll A z)))) ∧
    represent (high S (roll B z))=Lattice.gauge (v ∘ S.ratio.embed) (Lattice.pull t u (represent (high S (roll A z)))))→
    (∀ t:S.Choices,belt (rescaleFields A) (Camera.tax 2 (flask (fair S t (G:=G))))=belt (rescaleFields B) (Camera.tax 2 (flask (fair S t (G:=G))))) →
    belt (rescaleFields A) (china h C)=belt (rescaleFields B) (china h C):=by
 intro A B hA hB hX hV ht hz
 apply PowerSeries.ext
 intro e
 change tap e _ = tap e _
 let g : S.Choices := (fun _ => (S.patch.center, 1), fun _ => S.patch.center)
 apply belt_finite (rescaleFields A) (rescaleFields B) (fun r i => leaf S (C r i) (stick r) i)
     (tax 2 (flask (fair S g (G:=G)))) (china h C) e
 · exact fun i hi => china_focus h g hC hi
 · intro r i
   exact Cairn.lower_same S (stick r) i (hC.banner r i).path (hC.hold r i) (hC.weight r i)
     (hC.dial r i) (hC.banner r i).hair t (S.ratio.embed u) A B hA hB hX hV
     (ht.mono fun _ ⟨a, ha, _⟩ => ⟨a, ha⟩)
 · exact hz g
lemma glowing (s:Calendar G)(m p:ℕ)(h:s.BlockControl m p)(hC:Stable C)[Fintype I](t:Signed)(u:Site (s.schedule.side m p)) :
 let S:=s.op m p
 ;∀ A B:Strip (Epic S.patch G _) I, (∀ i,Pace (A i))→(∀ i,Pace (B i))→ roll A 0=0→ roll B 0=0→
 (∀ᶠ z in 𝓝 0,∃ v:Site (s.schedule.side (m+1) p)→G.El,
    represent (low S (roll B z))=Lattice.gauge v (Lattice.pull t (S.ratio.embed u) (represent (low S (roll A z)))) ∧
    represent (high S (roll B z))=Lattice.gauge (v ∘ S.ratio.embed) (Lattice.pull t u (represent (high S (roll A z)))))→
    belt (rescaleFields A) (china h.branches C)=belt (rescaleFields B) (china h.branches C):=by
 intro S A B hA hB hX hV ht

 apply blossom (s.op m p) h.branches hC t u A B hA hB hX hV ht fun z=>Tack.dress s m p h t u A B z hA hB hX hV ht
