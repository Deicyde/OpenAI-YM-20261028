import YM.Further.CURVED_GAUSSIAN_JETS.Meters
import YM.Further.CURVED_GAUSSIAN_JETS.Ports
import YM.Further.CURVED_GAUSSIAN_JETS.Sales
/-!
# Post-L awards: costs on ordered addresses and complete-halo currency
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.ChangeV
open Tracks Matrix Function Filter Jets Lattice Wilson RG Precision Push.Uniform SectorNext.Vacuum Set MeasureTheory
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {I : Type} [Fintype I] [DecidableEq I] {G : Gauge} {f c : Side} {a : I → Site f} {r : Ratio c f} {W : Windows I} {A : Jets.Field G c I} {V : Config G c} {p : Prices} {δ K σ : ℝ} (hδ : 0<δ) {k q m N : ℕ}

def impact (L : Side) (p : Prices) := (L.val + L.val + 1)^4 * p.tags
def paidHits (L : Side) (p : Prices) (R σ K : ℝ) (m N d : ℕ) := volumeCost m (impact L p) N * (mapCost R σ m p.tags*K)^3 * Real.exp (-(R/2)*N) * ((1/2:ℝ)^d)
structure Hits (a : I → Site f) (r : Ratio c f) (p : Prices) (σ K : ℝ) (m N : ℕ) : Prop where
  hit (d e : ℕ) : e ≤ d+2 → ∀ x : Site c,
    meter (r.parent ∘ a) σ m N x (ticket a p K N d (m:=e)) ≤ paidHits r.count p (spare p) σ K m N d
  half (d e : ℕ) : e ≤ d+2 → ∀ x : Site c,
    meter (r.parent ∘ a) σ m N x (fun z : Run I e=> Real.sqrt (ticket a p K N d z)) ≤ paidHits r.count p (spare p/2) σ (Real.sqrt K) m N d
lemma hit_time (m : ℕ) (p : Prices) (h : 1≤K) (hs : 0≤σ) : ∀ᶠ N : ℕ in atTop, ∀ {f c : Side} (r : Ratio c f) (I : Type) [Fintype I] (a : I → Site f), Multiplicity a p.tags → Hits a r p σ K m N := by
  have he := spare_pos p
  filter_upwards [paid_meter.{0} m p.tags he hs h,paid_meter.{0} m p.tags (half_pos he) hs (Real.one_le_sqrt.mpr h)] with N hN hN'
  intro f c r I _ a ha
  have hb := projection_count r ha
  refine ⟨fun d e h => hN _ _ ha hb h, fun d e hd x=>?_⟩
  simp_rw [←envelope_ticket,half_envelope (zero_le_one.trans h)]; exact hN' _ _ ha hb hd x

structure Award (a : I → Site f) (r : Ratio c f) (W : Windows I) (p : Prices) (hδ : 0<δ) (m k q N : ℕ) (K : ℝ) (V : Config G c) (A : Jets.Field G c I) : Prop where
  record (o : Site f) {t : ℝ} (ht : 0≤t) : Tracks.Record W p (rule a o q ht hδ) k N K V A (Due r.embed o q t)
  live₀ {d : ℕ} (z : Run I (d+1)) : ¬ Hops (r.parent ∘ a) (m*N) z → pushLog W A z=fun _=>0
  live {d : ℕ} (z : Run I (d+2)) : ¬ Hops (r.parent ∘ a) (m*N) z → (mailed W A z=fun _=>0) ∧ pushQuad W A z=fun _=>0



lemma coarse_due {u : Site f} {v : Directions G c} (h : ∀ i : Edge (Site c), ‖v i‖ ≤ ((1+separation (r.parent u) i.1:ℝ))^q) : Due r.embed u q ((2:ℝ)^q) v := by
  intro i
  have he := Work.E04.parent_separation r u (r.embed i.1); rw [r.embed_parent] at he
  unfold cap; rw [←mul_pow]; apply (h i).trans; gcongr
  have : (separation (r.parent u) i.1:ℝ) ≤ (separation u (r.embed i.1):ℝ)+1 := by exact_mod_cast he
  linarith [Nat.cast_nonneg (α:=ℝ) (separation u (r.embed i.1))]
lemma cap_transfer {d : ℕ} (x : Run I d) {j : ℕ} (hj : j≤k) : ((rule a (a (x 0)) q (show (0:ℝ) ≤ 2^q by positivity) hδ).τ (x 0))^j ≤ (2:ℝ)^(q*k) := by
  unfold rule cap; simp only [Function.comp_apply,separation_self,Nat.cast_zero,add_zero,one_pow,mul_one]; rw [pow_mul]; exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hj
def About (G : Gauge) (x : Site c) (q : ℕ) (l : Word G c) := ∀ i∈l,∀ e : Edge (Site c), ‖i e‖ ≤ ((1+separation x e.1:ℝ))^q
namespace Award
variable (h : Award a r W p hδ m k q N K V A) {l : Word G c} (hl : l.length≤k) {d : ℕ} (hK : 0≤K)
include h hl hK
lemma income (i : I) (hd : About G (r.parent (a i)) q l) : ‖leftDerivs (fun v=>W.tollLine (A v) p.mass i) l V‖ ≤ K*(2:ℝ)^(q*k) :=
    ((h.record (a i) _).amounts i l hl (fun _ hj=>coarse_due (hd _ hj))).trans (mul_le_mul_of_nonneg_left (cap_transfer hδ (fun _ : Fin (0+1)=>i) hl) hK)


end Award
end YM.Further.CurvedGaussianJets.ChangeV
