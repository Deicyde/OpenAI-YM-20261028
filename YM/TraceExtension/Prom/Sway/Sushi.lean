import YM.MergeProof.West.Sushi
import YM.TraceExtension.Prom.Sway.Price
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Atlas
open Lattice Wilson RG Station Set Labels Price  Glimmer Rise Normal Function Filter Cells Perch  Beamer Configuration Marker Glyph Common Particle Read Exponential
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {C : Family G} {d k N p n : ℕ}

lemma passingX_allSky (h : G.Simple) (hp : C.Makes) (degree : ℕ) {d0:Fin n→ℕ} (hY:∀ i,d0 i ≤ d) (u : (i:Fin n)→ C.label (d0 i)) : ∀ᶠ k in atTop, ∀ b : ℝ, 0 ≤ b → (∀ i, Atlas.saves C (d0 i)+3 ≤ b) → passingX hY u k degree b := by
  let Y:= C.path.levels
  let F := fun i => raiseLabel _ (hY i) ((C.labels.level (d0 i)).coords.symm (u i))
  let v := fun i => thawKey (F i)
  let A := (∑ i, Rise.coin (v i))+1
  have hh (i) : 0 ≤ coin (v i) := Rise.sign _ _ zero_le_one
  have hz : 1 ≤ A := by unfold A; linarith only [show 0 ≤ ∑ i, coin (v i) from Finset.sum_nonneg fun i _ => hh i]
  filter_upwards [eventually_all.mpr (fun i => loveSky h hp (u i)),(hat_rate Y h).eventually (shed n degree A hz), (hat_rate Y h).eventually (radiant (G:=G) (d:=d) (n:=n) degree)] with k h1 h2 h3 b hb hw
  obtain ⟨Q,hξ,hb₁,hP,hB,hc⟩ := h2
  intro N p hk M T H v₀ he
  let s:= clim Y k; let ρ:= mag Y b k
  have he' : 1 ≤ ρ := by unfold ρ;rw [mag_bill]; exact Glimmer.costed _ _ hb
  let I := (Subtype.val : trimV (lengthW s) G→ Address G)
  refine ⟨Q,hB,hP,hc, ⟨he', fun i => h1 i b hb _ _ hk degree (M i) (T i) (H i) (v₀ i) (he i), fun i => (H i).order _, fun i => ?_, fun _ z => ?_,Glimmer.costed _ _ (fuel_real degree n).le,fun i => ?_,?_⟩⟩
  · rw [hb₁]; exact (Finset.single_le_sum (f:=fun i => coin (v i)) (fun i _ => hh i) (Finset.mem_univ i)).trans (le_add_of_nonneg_right zero_le_one)
  · exact h3 _ I ρ he' z ((tracing _ _).mp z.property)
  · exact Perch.alignedX (hY i) I ρ (zero_lt_one.trans_le he') (he i) ((M i) _) ((H i).test _)
  intro i; rw [hξ]; change _ ≤ _* (Station.mag Y b k)^(d0 i+1); rw [mag_bill]; exact Glimmer.ticket degree n (d0 i) (Atlas.saves C (d0 i)) b (hw i) s
end YM.Next.Rank.Atlas
