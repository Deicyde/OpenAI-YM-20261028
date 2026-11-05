import YM.Next.RANK.Bird
import YM.Next.RANK.Memorandum

/-!
# Predetermined W budget with unscaled prices

P.p.B at this stop must be the auxiliary one. Meter supplies weights and uses
cube + restored marker stencil. Prove D owed even when nonconstant and when the
label hasn't yet had a projection budget beyond this stamp. No mask change for D.
Remaining W input is absolute UNweighted unscaled estimate against minus known D.
Later use follows from the full support prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Peak
open Lattice Wilson RG Value Perch Marker Glyph Cells Market Read Dock Camp Filter Station Extraction
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {m p k N v : ℕ}
variable {c : Demand} {z : ℝ} (A : Levels G) {i : ℕ}

-- s length cap consumed uniformly at same fixed stage.

def powder (s : ℝ) (m : ℕ) := bill (1/(8*m:ℝ)) s
lemma packaged : powder (A.clock.hatBeta k) m=Ship.allowance A m k := by
  unfold Ship.allowance Ship.pot Calendar.monitor powder bill boil y; rw [Real.log_exp]; congr 1; ring

def Meter {o : BudgetPoint} (ho : o.B=walls (A.clock.hatBeta i))
    (h : Shelf c m (A.clock.hatBeta k) (A.clock.hatBeta i)) : Change o m where
  e := c.e
  base := c.base
  spare := 1
  spare_cost := by norm_num
  fee := 4*boil (A.clock.hatBeta k)
  fee_cost := by exact mul_nonneg (by norm_num) (boil_pos _)
  narrow := c.U*boil (A.clock.hatBeta k)
  narrow_cost := mul_nonneg c.posU (boil_pos _)
  inside := c.V*boil (A.clock.hatBeta k)
  inside_cost := mul_nonneg c.posV (boil_pos _)
  reserve := 2 * Perch.join (A.clock.hatBeta i)
  reserve_cost := by dsimp only [Perch.join,hot]; positivity
  saving := boil (A.clock.hatBeta k)
  saves := boil_pos _
  local_pack := ho ▸ h.local_pack
  force_pack := ho ▸ h.force_pack
  radius := Ship.allowance A m k
  pos_r := Real.exp_pos _
  limit_c := bill 1 (A.clock.hatBeta k)
  first_c := (Real.exp_pos _).le
  limit_w := bill (-25/32) (A.clock.hatBeta k)
  first_w := (Real.exp_pos _).le
  output := bill (-3/4) (A.clock.hatBeta k)
  wing := 1
  yard := bill (-((m:ℝ)*c.V)-2) (A.clock.hatBeta k)
  weather := h.weather
  hit := Perch.gas c (A.clock.hatBeta i)
  γ := bill (-1) (A.clock.hatBeta k)
  main := (Real.exp_pos _).le
  force_hit := h.cash
  fits := ho ▸ h.fits

lemma aperture {n : Type} [Fintype n] [DecidableEq n] {V : Type} [Fintype V] [DecidableEq V] {o : BudgetPoint} (ho : o.B=walls (A.clock.hatBeta i))
    (h : Shelf c m (A.clock.hatBeta k) (A.clock.hatBeta i)) (x : n × flame V) (hv : Fintype.card V≤m) :
    Poly.toll (fun _ => (Meter A ho h).radius) (sectionAt x) ≤ bill (1/8) (A.clock.hatBeta k) := by
  let s := A.clock.hatBeta k; let a := powder s m
  simp only [Meter,← packaged,Poly.toll,Finset.prod_const]
  have ht : (sectionAt x).val.card ≤ m := by
    change ({x.1} ×ˢ x.2.val.val).card ≤ m; rw [Finset.card_product,Finset.card_singleton,one_mul]; exact (Finset.card_le_univ _).trans hv
  have hm : 0<m := lt_of_lt_of_le (by simpa [sectionAt,Glyph.push,scene] using! Finset.card_pos.mpr x.2.property) ht
  have he : a^m=bill (1/8) s := by
    dsimp only [a,powder,bill]; rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hA : 1 ≤ a := Real.one_le_exp (by have hx := boil_pos s; positivity)
  exact (pow_le_pow_right₀ hA ht).trans_eq he

lemma charged_cube {o : BudgetPoint} (Q : ℕ) {e : ℝ} (he : 0≤e) (i : Site n) :
    charge o e (halo (Q*o.B) {i}) ≤ Real.exp (e*((Q+Q+1:ℕ):ℝ)^4) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast Corona.tile i Q o.B o.B_pos) he)

-- At the station take an unweighted W estimate, signed compensation from
-- negatively connected value. Use Cube locally through all gauges.
section
variable {b : ℝ} {hN : k ≤ N} {A}
variable {D : Rep G (A.S.side (middle A b k) p)}
variable (u : Shelf c m (A.clock.hatBeta k) (A.clock.hatBeta (middle A b k))) (ho : D.p.B=walls (A.clock.hatBeta (middle A b k)))
variable {F : Points v}

lemma warming {ζ : Site (A.S.side (width A b k) p) × Fin v → Site (A.S.side (middle A b k) p)}
    {W : Site (A.S.side (width A b k) p) × flame (Fin v) → SourceAt G ζ}
    {C : Site (A.S.side (width A b k) p) × flame (Fin v) → ℂ}
    (hv : v ≤ m) (hw : ∀ i,(W i).extent=Peak.route A b k p c.Q D.p.B i.1)
    (hp : ∀ i,(W i).fires=sectionAt i)
    (hU : ∀ i U, Healthy D.p.threshold (Peak.route A b k p c.Q D.p.B i.1) U →
      ‖(W i).value U+C i‖ ≤ bill (-31/32) (A.clock.hatBeta k))
    (hV : ∀ i, ‖C i‖ ≤ bill (1/4) (A.clock.hatBeta k)) : Wells (Meter A ho u) W C (Peak.route A b k p c.Q D.p.B) := by
  let e := c.e; let s := A.clock.hatBeta k; let g := c.Q; let Y := Meter A ho u
  have he (i : Site (A.S.side (width A b k) p) × flame (Fin v)) {e : ℝ} (he : 0≤e) : charge D.p e (Peak.route A b k p g D.p.B i.1) * Poly.toll (fun _ => Y.radius) (sectionAt i) ≤
      Real.exp (e*((g+g+1:ℕ):ℝ)^4)*bill (1/8) s := mul_le_mul (charged_cube g he _) (aperture _ ho u i (by simpa using hv))
        (Poly.worth (fun _ => Y.pos_r) _).le (Real.exp_pos _).le
  have hz (e : ℝ) : 0 ≤ Real.exp (e*((g+g+1:ℕ):ℝ)^4)*bill (1/8) s := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  refine ⟨hp,hw, fun i U hh => (mul_le_mul (he i Y.base) (hU i U hh) (norm_nonneg _) (hz _)).trans u.wakes, ?_⟩
  intro i; exact (mul_le_mul (he i (add_nonneg Y.base zero_le_one)) (hV i) (norm_nonneg _) (hz _)).trans u.tree
end

variable {C : Family G} {X : Points v}

/-- D prices bounded uniformly on planned generic rounding. -/
def sufficiently (C : Family G) (B : Fin v→(standard C).Tag) (b : ℝ) (X : Points v) (k : ℕ) :=
    ∀ h : Fit C.path.levels b k X, ∀ p N (hi : k ≤ N) i,
      ‖view (Ship.yard C b hi p) (Ship.targets C B h) i‖≤ bill (1/4) (C.path.levels.clock.hatBeta k)

lemma cough (h : G.Simple) {b : ℝ} (hb : 0<b) (X : Points v) (hx : X∈generic _) (B : Fin v→ (standard C).Tag) :
    ∀ᶠ k in atTop, sufficiently C B b X k := by
  let Y := C.path.levels; let H := fun x : Points v => Read.maxProfile C x B
  let D := fun x => Exponential.roll (H x) (Fintype.card (Fin v))
  have ht : Tendsto (fun k => D (Station.tested Y b k X)) atTop (𝓝 (D X)) := by
    apply (Exponential.roll_cont _).continuousAt.tendsto.comp
      (profile_tends _ _ (Maxwell.table_smooth C.labels) (generic_conf _ hx) (Station.tuning Y X h hb))
  have he i : ∀ᶠ k : ℕ in atTop, ‖(D (Station.tested Y b k X)).part i‖ ≤ bill (1/4) (Y.clock.hatBeta k) := by
    have hx := ((tendsto_pi_nhds.1 ht i).norm).eventually (ge_mem_nhds (lt_add_one (‖(D X).part i‖)))
    filter_upwards [hx, ((bill_lo (a:=1/4) (by norm_num)).comp (hat_rate Y h)).eventually_ge_atTop (‖(D X).part i‖+1)] with k hp hq
    exact le_trans hp hq
  filter_upwards [eventually_all.mpr he] with k hf hh p N hi j
  let T := Ship.yard C b hi p
  have hv := Read.cumulative C (tested Y b k X) B (Ship.fitting hh)
  have hp : Ship.targets C B hh=D (tested Y b k X) := Exponential.Expands.uniq hv (Exponential.rolls _ (Read.profile_vac _ (Maxwell.table_regular C.labels) _ (Ship.fitting hh) B))
  rw [hp,view]; unfold Array.reorient; split_ifs <;> simpa only [shade_part, Poly.part_neg,norm_star,norm_neg] using! hf j.2.val
end YM.Next.Rank.Peak
