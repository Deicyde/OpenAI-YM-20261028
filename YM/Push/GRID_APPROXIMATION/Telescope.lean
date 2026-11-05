import YM.Next.FOUNDATIONS.SU2
import YM.Push.GRID_APPROXIMATION.Picture
import YM.Push.GRID_APPROXIMATION.Translate


/-!
# Estimates for entire ordinary products on the fixed grid

Sets of alternative monomials not conflated. Price before root based on
cells of this actual h-tiling. Keep arrays common for subsequent flash
comparison at the same cost station. Doesn't use sup at *that* varying
station to get small errors. Expansion keeps a factor of rooted savings for
each actual difference slot. Compares even all finite distinct centered
placements on this torus simultaneously.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson MeasureTheory Function Filter Set Cells
open scoped Topology BigOperators

variable {G : Gauge} {ι : Type*} [Fintype ι]

private lemma place_prod {M : Type*} [CommSemiring M] [DecidableEq ι] (f g : ι → M) :
    ∏ i, (f i + g i) = ∑ l∈(Finset.univ:Finset ι).powerset, ∏ i, if i∈l then f i else g i := by
  rw [Finset.prod_add]; refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.prod_ite]
  have ha : Finset.univ.filter (fun i => i∈l) = l := by ext; simp
  have hb : Finset.univ.filter (fun i => ¬ i∈l) = Finset.univ \ l := by ext; simp
  rw [ha,hb]

/-- Already lets one linearize quantitative prices, empty product included. -/
lemma tariff (S : Schedule) {h N p : ℕ} (hh : h≤N) (β : ℝ) (H : Seam G (S.side N p) β)
    (a : ι → Site (S.side h p)) (hc : Injective a)
    (O Z : ι → Config G (S.side N p) → ℂ) (c e : ι → ℝ)
    (hf : ∀ i, Interior ((tilesAt S p hh).chamber 0) (O i))
    (hF : ∀ i, Interior ((tilesAt S p hh).chamber 0) (Z i))
    (hO : ∀ i, (tilesAt S p hh).rootTest β (O i) ≤ c i)
    (hZ : ∀ i, (tilesAt S p hh).rootTest β (Z i-O i) ≤ e i) :
    ‖moment β (fun U => ∏ i, Z i (translate (anchor S p hh (a i)) U)) -
      moment β (fun U => ∏ i, O i (translate (anchor S p hh (a i)) U))‖ ≤ ∏ i, (e i+c i) - ∏ i, c i := by
  classical
  let T := tilesAt S p hh
  let W (l : Finset ι) (i) := if i ∈ l then Z i-O i else O i
  let b (l : Finset ι) := ∏ i, if i∈l then e i else c i
  let C (F : ι → Config G (S.side N p) → ℂ) (U : Config G _) := ∏ i,F i (translate (anchor S p hh (a i)) U)
  have hI (l : Finset ι) (i : ι) : Interior (T.chamber 0) (W l i) := by
    unfold W; split
    · rw [sub_eq_add_neg]; exact (hF i).plus (show Interior _ (fun U => -(O i U)) from by simpa using (hf i).scale (-1))
    exact hf i
  have hj (t) : Integrable (C (W t)) (law G (S.side N p) β) := by
    have he (i : ι) : Envelope (fun U : Config G _ => W t i (translate (anchor S p hh (a i)) U)) :=
      (cylinder_env (hI t i)).comp_env (law_translate β _).measurable
    exact (Envelope.prodC _ _ (fun i _ => he i)).integrableC _
  let L := (Finset.univ:Finset ι).powerset
  let X (l) := moment β (C (W l))
  have he (U) : C Z U = ∑ l∈L, C (W l) U := by
    have hx (i : ι) (U : Config G (S.side N p)) (l) : W l i U = if i∈l then (Z i-O i) U else O i U :=
      apply_ite (fun F : Config G (S.side N p) → ℂ => F U) _ _ _
    unfold C L; simp_rw [hx]
    rw [← place_prod]; simp
  have hy : moment β (C Z) = ∑ l∈L, X l := by
    unfold moment; simp_rw [he]; exact integral_finsetSum _ (fun l _ => hj l)
  have hd : W ∅ = O := by ext; simp [W]
  have hx : X ∅=moment β (C O) := by unfold X; rw [hd]
  have hp : (∅ : Finset ι)∈L := by simp [L]
  have hB (l) : ‖X l‖ ≤ b l := by
    refine (rooted_translates S hh β H a hc (W l) (hI l)).trans (Finset.prod_le_prod
      (fun i _ => T.root_nonneg ..) (fun i _ => ?_))
    unfold W; split_ifs
    · exact hZ i
    exact hO i
  change ‖moment β (C Z) - moment β (C O)‖ ≤ _
  rw [hy, place_prod e c]; change ‖_‖ ≤ (∑ l∈L, b l)-∏ i,c i
  rw [←Finset.sum_erase_add L X hp,hx,add_sub_cancel_right,
    ← Finset.sum_erase_add L b hp,show b ∅ = ∏ i,c i by simp [b],add_sub_cancel_right]
  exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => hB i)

variable {C : Family G} {v : ι → C.book.Token} {h : ℕ}

def volume0 (Z : ∀ i, Figures C (v i) h) := ∏ i, ((Z i).cap 0+(Z i).err 0)
def volume1 (Z : ∀ i, Figures C (v i) h) (q) := ∏ i, ((Z i).err q + ((Z i).cap 0+(Z i).err 0))

def expense (Z : ∀ i, Figures C (v i) h) (q) := volume1 Z q - volume0 Z

lemma expense_zero (Z : ∀ i, Figures C (v i) h) {f : Extraction.Order}
    (hz : ∀ i, (Z i).Gives f) : Tendsto (expense Z) atTop (𝓝 0) := by
  let x (i : ι) := (Z i).cap 0+(Z i).err 0
  have ht : Tendsto (volume1 Z) atTop (𝓝 (volume0 Z)) := by
    have he i : Tendsto (fun q => (Z i).err q + x i) atTop (𝓝 (x i)) := by
      simpa only [zero_add] using (hz i).cost.add_const (x i)
    exact tendsto_finsetProd _ fun i _ => he i
  simpa only [sub_self] using! ht.sub_const (volume0 Z)

/-- For production q we charge original O to production 0. No integral at
the reconstruction phases. -/
lemma paid_at (Z : ∀ i, Figures C (v i) h) (H : C.Makes) (q N p) (hh : h≤N)
    (ht : ∀ i (a : ℕ), a ∈ ({q,0}:Finset ℕ) → PictureAt C (v i) h N p ((Z i).plot a N p) ((Z i).cap a) ((Z i).err a) ((Z i).radius a))
    (hf : ∀ i, 0 ≤ (Z i).cap 0) (a : ι → Site (C.side h p)) (ha : Injective a) :
    ‖moment (C.beta N p) (fun U => ∏ i, (Z i).plot q N p (translate (anchor C.S p hh (a i)) U)) -
      moment (C.beta N p) (fun U => ∏ i, C.seen (v i) (anchor C.S p hh (a i)) U)‖ ≤ expense Z q := by
  let T := tilesAt C.S p hh
  have hv i := ht i 0 (by simp)
  have hw i := ht i q (by simp)
  let F (i : ι) := (Z i).plot q N p
  let O (i : ι) := C.seen (v i) (0:Site (C.side N p))
  have he := tariff C.S hh (C.beta N p) (seamless H N p) a ha O F (fun i => (Z i).cap 0+(Z i).err 0)
    (fun i => (Z i).err q) (fun i => (hv i).source) (fun i => (hw i).target)
    (fun i => (hv i).budget H (hf i)) (fun i => (hw i).cost)
  unfold O Family.seen at he
  simp only [C.translation,zero_add] at he; exact he
end YM.Push.GridApprox
