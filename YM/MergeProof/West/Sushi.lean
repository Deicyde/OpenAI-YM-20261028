import YM.MergeProof.West.Latte
import YM.MergeProof.West.Teddy
import YM.Next.RANK.ParticleGate
import YM.Next.RANK.Stories


set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Atlas
open Lattice Wilson RG Station Set Labels Price  Glimmer Rise Normal Function Filter Cells Perch  Beamer Configuration Marker Glyph Common Particle Read Exponential
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {C : Family G} {d k N p n : ℕ}

def passingX {d0:Fin n→ℕ} (hY:∀ i,d0 i ≤ d) (u : (i:Fin n)→ C.label (d0 i)) (k degree : ℕ) (b : ℝ) :=
    let Y:= C.path.levels
    let s := clim Y k; let ρ:= Station.mag Y b k
    let ply:= lengthW s
    let F:= fun i => raiseLabel _ (hY i) ((C.labels.level (d0 i)).coords.symm (u i))
    let I:= (Subtype.val : trimV ply G → _)
    ∀ N (p : ℕ) (_ : k≤N) (M : (i:Fin n)→ Heater C k (d0 i))(T:(i:Fin n)→Module.End ℂ (C.label (d0 i))), (∀ i, Heating C k N p (d0 i) degree (M i) (T i)) → ∀ v : (i:Fin n)→ C.label (d0 i), (∀ i : Fin n, Price.Solves C ρ (d0 i) k N p (T i) (u i) (v i)) →
      ∃ X : Spend n degree, X.B=bill (fuel degree n) s ∧ X.collision=bill (-2) s ∧ X.cost=bill (-3/2) s ∧
        TollsX X d0 (fun _ : Fin n => features d I ρ) (fun i => M i (v i)) F ρ (fun i=> bill (b*d0 i+saves C (d0 i)) s) (bill (fuel degree n) s)

lemma passingX_all (h : G.Simple) (hp : C.Makes) (degree : ℕ) {d0:Fin n→ℕ} (hY:∀ i,d0 i ≤ d) (u : (i:Fin n)→ C.label (d0 i)) (b : ℝ) (hb : 0<b)
    (hw : ∀ i, Atlas.saves C (d0 i)+3 ≤ b) : ∀ᶠ k in atTop, passingX hY u k degree b := by
  let Y:= C.path.levels
  let F := fun i => raiseLabel _ (hY i) ((C.labels.level (d0 i)).coords.symm (u i))
  let v := fun i => thawKey (F i)
  let A := (∑ i, Rise.coin (v i))+1
  have hh (i) : 0 ≤ coin (v i) := Rise.sign _ _ zero_le_one
  have hz : 1 ≤ A := by unfold A; linarith only [show 0 ≤ ∑ i, coin (v i) from Finset.sum_nonneg fun i _ => hh i]
  filter_upwards [eventually_all.mpr (fun i => love b hb h hp (u i)),(hat_rate Y h).eventually (shed n degree A hz), (hat_rate Y h).eventually (radiant (G:=G) (d:=d) (n:=n) degree)] with k h1 h2 h3
  obtain ⟨Q,hξ,hb₁,hP,hB,hc⟩ := h2
  intro N p hk M T H v₀ he
  let s:= clim Y k; let ρ:= mag Y b k
  have he' : 1 ≤ ρ := by unfold ρ;rw [mag_bill]; exact Glimmer.costed _ _ hb.le
  let I := (Subtype.val : trimV (lengthW s) G→ Address G)
  refine ⟨Q,hB,hP,hc, ⟨he', fun i => h1 i _ _ hk degree (M i) (T i) (H i) (v₀ i) (he i), fun i => (H i).order _, fun i => ?_, fun _ z => ?_,Glimmer.costed _ _ (fuel_real degree n).le,fun i => ?_,?_⟩⟩
  · rw [hb₁]; exact (Finset.single_le_sum (f:=fun i => coin (v i)) (fun i _ => hh i) (Finset.mem_univ i)).trans (le_add_of_nonneg_right zero_le_one)
  · exact h3 _ I ρ he' z ((tracing _ _).mp z.property)
  · exact Perch.alignedX (hY i) I ρ (zero_lt_one.trans_le he') (he i) ((M i) _) ((H i).test _)
  intro i; rw [hξ]; change _ ≤ _* (Station.mag Y b k)^(d0 i+1); rw [mag_bill]; exact Glimmer.ticket degree n (d0 i) (Atlas.saves C (d0 i)) b (hw i) s
end YM.Next.Rank.Atlas
