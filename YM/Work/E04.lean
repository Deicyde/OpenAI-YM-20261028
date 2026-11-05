import YM.Bid.Energy
import YM.Corona.Spend

/-!
E04: localized absolute path series, pre-L lane prices and the
selector + transpose budget, separately within each orientation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.E04

open YM.Bid Lattice RG Wilson YM.Pressure YM.Pressure.Stores YM.Pressure.Teller Filter Finset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {n m c f : Side}

lemma slope_nonneg (G : Gauge) : 0 ≤ G.slopeConstant := by
  have ht (x : G.Color) : 0 ≤ - LinearMap.trace ℝ G.Color (G.ad x ∘ₗ G.ad x) := by
    change 0 ≤ G.minusKilling x x
    rw [Gauge.minusKilling_sq _ (EuclideanSpace.basisFun G.ColorIndex ℝ)]
    exact sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold Gauge.slopeConstant
  have hc : 0 ≤ G.casimir := div_nonneg (neg_nonneg.mpr (sum_nonpos fun i _ ↦ neg_nonneg.mp (ht _))) (by positivity)
  positivity

lemma shift_nonneg (G : Gauge) (L : Side) : 0 ≤ G.slopeConstant * Real.log L.val := by
  refine mul_nonneg (slope_nonneg G) (Real.log_nonneg ?_)
  exact_mod_cast (L.property : 1 ≤ L.val)

lemma temp_nonneg (x : ℝ) : 0 ≤ temp x := by unfold temp; positivity

lemma eventually_temp_le (a : ℝ) (ha : 0 ≤ a) : ∀ᶠ x : ℝ in atTop, temp x ≤ 2 * temp (x+a) := by
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop a, Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with x h0 hx hl
  have hp := Real.sqrt_pos.2 h0
  have hq := Real.sqrt_pos.2 (show 0<x+a by linarith)
  have hg : Real.sqrt (x+a) ≤ 2 * Real.sqrt x := by
    nlinarith only [Real.sq_sqrt h0.le, Real.sq_sqrt (show 0 ≤ x+a by linarith), hx, hp, hq]
  have hi : (Real.sqrt x)⁻¹ ≤ 2*(Real.sqrt (x+a))⁻¹ := by
    simpa only [one_div, div_eq_mul_inv, one_mul] using (div_le_div_iff₀ hp hq).2 (show 1*Real.sqrt (x+a) ≤ 2 * Real.sqrt x by simpa only [one_mul])
  rw [temp,temp,← mul_assoc]
  gcongr
  · exact Real.log_nonneg hl
  · exact le_add_of_nonneg_right ha

lemma eventually_room (a r : ℝ) (hr : 0 < r) : ∀ᶠ x : ℝ in atTop,
    till x + 1 ≤ radiusB x/50 ∧ ∀ k : ℕ, temp (x+a)*Real.exp (k/r) < 2 → k+1 ≤ radiusB x/50 := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (100*r+100)),
    eventually_ge_atTop (8:ℝ), eventually_ge_atTop a, eventually_gt_atTop (-a)] with x hl hx ha hy
  have hB : Real.log x ^2 ≤ radiusB x := Nat.le_ceil _
  have hp := Real.sqrt_pos.2 (show 0 < x+a by linarith)
  have hq : 2 * Real.sqrt (x+a) ≤ x := by
    nlinarith only [Real.sq_sqrt (show 0≤x+a by linarith),ha,hx,hp]
  constructor
  · unfold till
    have : (100:ℝ) ≤ radiusB x := by nlinarith only [hB,hl,hr]
    have : 100 ≤ radiusB x := by exact_mod_cast this
    omega
  intro k hk
  have he : (Real.sqrt (x+a))⁻¹ ≤ temp (x+a) :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_exp (sq_nonneg _))
  have he' := (mul_le_mul_of_nonneg_right he (Real.exp_pos (k/r)).le).trans_lt hk
  have hlog : (k:ℝ)/r < Real.log x := Real.exp_lt_exp.mp (by
    rw [Real.exp_log (by linarith)]
    exact lt_of_lt_of_le ((div_lt_iff₀ hp).mp (by simpa [div_eq_mul_inv,mul_comm] using he')) hq)
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  have : ((k:ℝ)+1)*50 ≤ ↑(radiusB x) := by
    nlinarith [(div_lt_iff₀ hr).mp hlog]
  exact_mod_cast this

lemma stop_separation_le (x : Site n) (w : Walk) : separation x (stop x w) ≤ w.length := by
  induction w generalizing x with
  | nil => simp [stop]
  | cons s w ih =>
    have h : separation x (x + s.vec) ≤ 1 := by
      rw [separation_comm,separation, add_comm,add_sub_cancel_right, Step.vec]; split
      · rw [pdist_neg]; exact pdist_step _
      · exact pdist_step _
    have hv := separation_triangle x (x+s.vec) (stop (x+s.vec) w)
    dsimp only [stop, List.length_cons]; grind

lemma slot_separation (a : Slot) (x : Site n) : separation x (wrap n a.offset+x) ≤ a.length := by
  rw [show separation x _ = separation 0 (wrap n a.offset) by simpa only [zero_add] using separation_translate (0:Site n) (wrap n a.offset) x, Slot.offset, wrap_stop_cover,map_zero]
  exact (stop_separation_le _ a.walk).trans (by unfold Slot.length; omega)

lemma parent_separation (q : Ratio m n) (x y : Site n) : separation (q.parent x) (q.parent y) ≤ separation x y+1 := by
  refine Nat.le_of_mul_le_mul_left ((Corona.foreshorten q x y).trans ?_) q.count.property
  rw [Nat.mul_succ]; exact Nat.add_le_add_right (Nat.le_mul_of_pos_left _ q.count.property) _

-- Keep the full label index even for coincident cells on the torus.
def landing (s : Slot) (x : Site n) : Cell n := (wrap n s.offset+x,s.plaq)

def rich (T : PathData G) (σ : ℝ) (a : PlaqAxes) (i : ℕ) := |(T.row a i).1| * Real.exp (σ * (T.row a i).2.length)

def grain (T : PathData G) (R d : ℕ) (p u : Cell n) (i : ℕ) :=
  let e := T.row p.2 i
  if d*e.2.length ≤ R ∧ landing e.2 p.1 = u then |e.1| else 0

section Row
variable (T : PathData G) (R d : ℕ)

lemma crunch_eq (p u : Cell n) : crunch T R d p u = ∑' i, grain T R d p u i := by
  rcases u with ⟨x,a⟩; simp only [crunch,grain,landing,Prod.mk.injEq,and_comm (a := _ = x) (b := _ = a)]

lemma grain_nonneg (p u : Cell n) (i) : 0 ≤ grain T R d p u i := by unfold grain; dsimp only; split <;> positivity

lemma grain_le_rich {σ : ℝ} (hσ : 0 ≤ σ) (p u : Cell n) (i) : grain T R d p u i ≤ rich T σ p.2 i := by
  unfold grain rich; dsimp only; split
  · exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity))
  · positivity

variable {T} {a : Stage} {Λ : ℝ} (h : T.Bounds a.clip a.width a.paths Λ)

include h in
lemma grain_summable (p u : Cell n) : Summable (grain T R d p u) :=
  (h.rows p.2).2.1.of_nonneg_of_le (grain_nonneg T R d p u) (grain_le_rich T R d h.width.le p u)

lemma grain_sum (z : Cell n → ℝ) (p : Cell n) (i : ℕ) :
    let e := T.row p.2 i
    ∑ u,grain T R d p u i * z u = if d*e.2.length ≤ R then |e.1| * z (landing e.2 p.1) else 0 := by
  dsimp only
  split_ifs with hk <;> simp [grain,hk,ite_mul]

include h in
lemma priced_sum (z : Cell n → ℝ) (p : Cell n) :
    ∑ u, crunch T R d p u * z u = ∑' i, ∑ u, grain T R d p u i*z u := by
  simp_rw [crunch_eq, ← tsum_mul_right]; symm
  exact Summable.tsum_finsetSum fun u _ ↦ (grain_summable R d h p u).mul_right (z u)

lemma grain_reached {p u : Cell n} (hk : 0 < crunch T R d p u) :
    ∃ i, d * (T.row p.2 i).2.length ≤ R ∧ landing (T.row p.2 i).2 p.1 = u := by
  by_contra! hn
  rw [crunch_eq] at hk
  have hh (i : ℕ) : grain T R d p u i = 0 := if_neg fun he => hn i he.1 he.2
  simp [hh] at hk

include h in
lemma priced_le (z : Cell n → ℝ) (p : Cell n) {t : ℝ} (ht : 0 ≤ t)
    (hz : ∀ s : Slot, z (landing s p.1) ≤ Real.exp (a.width * s.length)*t) :
    ∑ u, crunch T R d p u * z u ≤ a.paths * t := by
  rw [priced_sum R d h]
  obtain ⟨-,h1,h2⟩ := h.rows p.2
  change Summable (rich T a.width p.2) at h1
  have hs := summable_sum (s:=univ) fun u _ ↦ (grain_summable R d h p u).mul_right (z u)
  refine le_trans (hs.tsum_le_tsum (fun i ↦ ?_) (h1.mul_right t)) ?_
  · rw [grain_sum]; unfold rich; rw [mul_assoc]; split
    · exact mul_le_mul_of_nonneg_left (hz _) (abs_nonneg _)
    positivity
  · rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h2 ht

lemma back_grain_le (σ : ℝ) (hσ : 0 ≤ σ) (p : Cell n) (i : ℕ) :
    ∑ u, grain T R d u p i ≤ ∑ a : PlaqAxes, rich T σ a i := by
  unfold Cell Face; rw [Fintype.sum_prod_type,Finset.sum_comm]
  refine sum_le_sum fun a _ ↦ ?_
  let x := p.1 - wrap n (T.row a i).2.offset
  calc
    ∑ b : Site n, grain T R d (b,a) p i ≤ ∑ b : Site n, if x=b then rich T σ a i else 0 := by
      apply sum_le_sum; intro b _; split_ifs with hb
      · exact grain_le_rich T R d hσ (b,a) p i
      unfold grain; dsimp only; rw [if_neg]; intro hz
      have he : wrap n (T.row a i).2.offset+b = p.1 := congr_arg Prod.fst hz.2
      exact hb (by dsimp [x]; rw [← he]; abel)
    _ = rich T σ a i := by simp

include h in
lemma back_sum_le (p : Cell n) : ∑ u, crunch T R d u p ≤ Fintype.card PlaqAxes * a.paths := by
  have hs := summable_sum (s:=univ) fun u _ ↦ grain_summable R d h u p
  have hs' (i : PlaqAxes) : Summable (rich T a.width i) := (h.rows i).2.1
  simp_rw [crunch_eq]
  rw [← Summable.tsum_finsetSum (fun u _ ↦ grain_summable R d h u p)]
  apply (hs.tsum_le_tsum (back_grain_le R d a.width h.width.le p) (summable_sum fun i (_ : i ∈ univ) ↦ hs' i)).trans
  rw [Summable.tsum_finsetSum (fun i _ ↦ hs' i)]
  simpa only [rich,sum_const,card_univ,nsmul_eq_mul] using (sum_le_sum (s:=univ) fun i _ ↦ (h.rows i).2.2)

include h in
lemma shorten_valued (p : Cell n) (U : Config G n) :
    ‖shorten T R d U p‖ ≤ ∑ u, crunch T R d p u * toll U u := by
  rw [shorten,priced_sum R d h]
  have hs : Summable fun i => ‖shortenTerm T R d U p i‖ :=
    (T.ell_dominated h p).absolute U |>.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun i => by
      unfold shortenTerm; split; rfl
      simp)
  apply (norm_tsum_le_tsum_norm hs).trans
  refine hs.tsum_le_tsum (fun i ↦ ?_) (summable_sum fun u _ ↦ (grain_summable R d h p u).mul_right (toll U u))
  rw [grain_sum, shortenTerm, Nat.mul_comm]; split_ifs with hk
  · rw [PathData.ellTerms, norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    let s := (T.row p.2 i).2
    have hg : faceValue (expandAt p.1 U) (s.offset,s.plaq)=faceValue U (landing s p.1) := travel_at ..
    rw [Slot.atSite, Slot.eval,G.norm_adjoint]; rw [hg]; exact G.curvature_norm _
  · exact norm_zero.le

include h in
lemma shorten_small (p : Cell n) {t : ℝ} (ht : 0 ≤ t) (U : Config G n) (hk : PathData.kept a.clip t p.1 U) :
    ‖shorten T R d U p‖ ≤ a.paths*t := by
  apply (shorten_valued R d h p U).trans
  refine priced_le R d h (toll U) p ht (fun s ↦ (hk (landing s p.1)).trans ?_)
  rw [mul_comm t]; gcongr ?_ * _; apply Real.exp_monotone
  apply (div_le_iff₀ a.clip.radius_pos).mpr
  have hq : (separation p.1 (landing s p.1).1 : ℝ) ≤ s.length := by exact_mod_cast slot_separation s p.1
  calc
    _ ≤ (s.length : ℝ) := hq
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right a.slow_selector (Nat.cast_nonneg (α:=ℝ) s.length)]
end Row

/-- A pre-L common upper bound for single-stage ℓ rows, columns and the clamp scale. -/
def capacity (a : Stage) := ((Fintype.card PlaqAxes : ℝ)+1)*a.paths + Real.sqrt a.clip.direct

lemma capacity_ge (a : Stage) : a.paths ≤ capacity a ∧ (Fintype.card PlaqAxes : ℝ) * a.paths ≤ capacity a ∧ Real.sqrt a.clip.direct ≤ capacity a := by
  have hp := a.paths_pos.le
  have hq := Real.sqrt_nonneg a.clip.direct
  have hh := mul_nonneg (Nat.cast_nonneg (α:=ℝ) (Fintype.card PlaqAxes)) hp
  unfold capacity; constructor; linarith
  constructor <;> linarith

lemma capacity_pos (a : Stage) : 0 < capacity a := lt_of_lt_of_le a.paths_pos (capacity_ge a).1

lemma lanes {T : PathData G} {a : Stage} {x t Λ A : ℝ} {d : ℕ} (h : T.Bounds a.clip a.width a.paths Λ)
    (hA : capacity a ≤ A) (ht : 0 ≤ t) (hd : 0 < d) {q : Site n → Site m}
    (hq : ∀ b e, separation (q b) (q e) ≤ separation b e + 1)
    (hroom : till x + 1 ≤ radiusB x/50 ∧
      ∀ k : ℕ, t*Real.exp (k/a.clip.relaxation) < 2 → k+1 ≤ radiusB x/50) : LaneCounts T x t a.clip A d q where
  attic p u := by rw [crunch_eq]; exact tsum_nonneg (grain_nonneg _ _ _ p u)
  finite p := by
    have hh := priced_le (till x) d h (fun _ => (1:ℝ)) p (by norm_num : (0:ℝ)≤1)
      (fun s => by simpa only [mul_one] using Real.one_le_exp (mul_nonneg h.width.le (Nat.cast_nonneg s.length)))
    simp_rw [mul_one] at hh; exact hh.trans ((capacity_ge a).1.trans hA)
  back p := (back_sum_le _ _ h p).trans ((capacity_ge a).2.1.trans hA)
  maps p u hk := by
    obtain ⟨i, hi, he⟩ := grain_reached _ _ hk
    have hf := congr_arg Prod.fst he
    have H : separation p.1 u.1 ≤ (T.row p.2 i).2.length := hf ▸ slot_separation _ _
    exact (hq _ _).trans ((Nat.add_le_add_right (H.trans ((Nat.le_mul_of_pos_left _ hd).trans hi)) 1).trans hroom.1)
  valued := shorten_valued _ _ h
  keeps V p hV := (shorten_small _ _ h _ ht V hV).trans (mul_le_mul_of_nonneg_right ((capacity_ge a).1.trans hA) ht)
  dropped V i j he := (hq ..).trans (hroom.2 _ (he.trans_le (G.chord_le_two _)))

lemma thinned_le {T : PathData G} {x t A : ℝ} {d : ℕ} {q : Site n → Site m} {c : Clip}
    (hA : Real.sqrt c.direct ≤ A) (ht : 0 ≤ t) (h : LaneCounts T x t c A d q) (V : Config G n) (p : Twin n) :
    ‖thinned T c t d (till x) V p‖ ≤ A*t := by
  have hA0 := (Real.sqrt_nonneg _).trans hA
  unfold thinned; split_ifs with hb hk hr
  · exact h.keeps V p.1 hk
  · rw [norm_zero]; positivity
  · have he := G.curvature_norm (faceValue V p.1)
    change _ ≤ toll V p.1 at he; rw [hr] at he
    rw [shoot, norm_le_zero_iff.mp he,smul_zero,smul_zero,norm_zero]; positivity
  · have hp : 0 < toll V p.1 := (G.chord_nonneg _).lt_of_ne' hr
    rw [shoot,norm_smul,norm_smul,Real.norm_of_nonneg (le_min (by norm_num) (by positivity)),Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hh : t/toll V p.1*(A*toll V p.1)=A*t := by field_simp
    apply le_trans ?_ hh.le
    gcongr
    · exact min_le_right ..
    exact G.curvature_norm _

lemma zip_le {α β : Type*} [Fintype α] [Fintype β] (g : α→β→Pay G) (a : β → G.Color) {C D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ b, ‖a b‖ ≤ D) (p : α) (hh : ∑ b, ‖g p b‖ ≤ C) : ‖zip g a p‖ ≤ C*D := by
  unfold zip; apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ b, ‖g p b‖*D := sum_le_sum fun b _ ↦ ((g p b).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hv b) (norm_nonneg _))
    _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hh hD

lemma max_paid {S : StepData c f} {T : Tube G S} {V : Config G c} {x C A : ℝ}
    (hC : 0 ≤ C) (hA : Real.sqrt T.low.direct ≤ A)
    (he : temp x ≤ 2 * fiery G x S.patch.L)
    (h : Allowance C T x V) (hl : LaneCounts T.down x (temp x) T.low A S.patch.L.val (id : Site c → Site c)) :
    Maximum (2*A*(1+C)) T x V := by
  have hA0 := (Real.sqrt_nonneg _).trans hA
  let t := fiery G x S.patch.L
  have ht : 0 ≤ t := temp_nonneg _
  have hv (b : Twin c) : ‖T.vision (till x) (temp x) V b‖ ≤ 2*A*t := by
    apply (thinned_le hA (temp_nonneg x) hl V b).trans
    linarith only [mul_le_mul_of_nonneg_left he hA0]
  have h1 : 2*A ≤ 2*A*(1+C) := le_mul_of_one_le_right (by positivity) (by linarith only [hC])
  have h2 : C*(2*A) ≤ 2*A*(1+C) := by linarith only [hA0]
  constructor
  · exact fun b ↦ (hv b).trans (mul_le_mul_of_nonneg_right h1 ht)
  · intro b; apply (zip_le _ _ (by positivity : 0 ≤ 2*A*t) hv b (h.wide.rows b)).trans
    rw [show C/(S.patch.L.val:ℝ)^2*(2*A*t) = (C*(2*A))/(S.patch.L.val:ℝ)^2*t by ring]; gcongr
  · intro b; apply (zip_le _ _ (by positivity : 0 ≤ 2*A*t) hv b (h.narrow.rows b)).trans
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h2 ht

theorem answer : YM.Bid.E04 := by
  intro E G P
  obtain ⟨C,hC,H⟩ := E P
  let A := capacity P.top + capacity P.below
  have hA : 0 < A := add_pos (capacity_pos _) (capacity_pos _)
  refine ⟨2*A*(1+C), by positivity,fun L W => ⟨?_⟩⟩
  let a := G.slopeConstant * Real.log L.val
  filter_upwards [(H L W).late, eventually_temp_le a (shift_nonneg G L),
    eventually_room a P.top.clip.relaxation P.top.clip.radius_pos,
    eventually_room 0 P.below.clip.relaxation P.below.clip.radius_pos] with x hx he htop hbelow
  simp only [add_zero] at hbelow
  intro c f S hL hs T hT F A' U k V hS hP
  obtain ⟨a',b',h,h'⟩ := hT.feeds
  have hup (D : ℝ) (hd : A ≤ D) : LaneCounts T.up x (fiery G x L) T.high D 1 S.ratio.parent := by
    rw [hT.high]
    exact lanes h ((le_add_of_nonneg_right (capacity_pos _).le).trans hd) (temp_nonneg _) (by decide)
      (parent_separation _) htop
  have hdown (D : ℝ) (hd : A ≤ D) : LaneCounts T.down x (temp x) T.low D L.val (id : Site c → Site c) := by
    rw [hT.low]
    exact lanes h' ((le_add_of_nonneg_left (capacity_pos _).le).trans hd) (temp_nonneg _) L.property
      (fun i j => Nat.le_succ _) hbelow
  have hd : A ≤ 2*A*(1+C) := by nlinarith only [hA,hC]
  refine ⟨hup _ hd,hdown _ hd,?_⟩
  refine max_paid hC.le ?_ (hL.symm ▸ he) (hx c f S hL hs T hT F A' U k V hS hP) ?_
  · rw [hT.low]; exact (capacity_ge _).2.2.trans (le_add_of_nonneg_left (capacity_pos _).le)
  · simpa only [hL] using hdown A le_rfl
end YM.Work.E04
