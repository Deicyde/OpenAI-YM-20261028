import YM.Next.FLUCTUATIONS.Slots
import YM.SectorNext.LARGE_FIELD_REMAINDERS.AffineBond


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# WorkF and WorkI minus true reference affine squares

Not spending any assigned rows. Genuine stack path-data tails, \\bar V
transports in the affine only. One channel already in actual positive
orientation, no change of Q convention. Polynomial in the true cut-radius
charged even after truncation achieved. Not differentiating s profiles, K etc.
No assumption that the subtracted row is resolved in the Gaussian integration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial  Next.Fluctuations Scales Metric   Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical  ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}

def firstFace (W : Config G n) (a : Directions G n) (i : Cell n) := G.curvature (faceValue W i)+faceVar W a i

def firstSlot (W : Config G f) (a : Directions G f) (s : Slot) (x : Site f) :=
  G.adjoint (travel W x s.walk) (firstFace W a (Work.F03.slotFace s x))

def perCharge (T : PathData G) (R : ℕ) (W : Config G f) (a : Directions G f) (i : Cell f) (j : ℕ) :=
  let F := T.row i.2 j
  if F.2.length ≤ R then F.1 • firstSlot W a F.2 i.1 else 0

def firstCut (T : PathData G) (R : ℕ) (W : Config G f) (a : Directions G f) (i : Cell f) :=
  ∑' j, perCharge T R W a i j

def affF0 (T : Tube G S) (R : ℕ) (s : ℝ) (V : Config G c) (W : Config G f) (a : Directions G f) (i : Cell f) :=
  Real.sqrt T.high.direct • firstFace W a i - T.Mv R s V (i,false)

def affF1 (T : Tube G S) (R : ℕ) (s : ℝ) (V : Config G c) (W : Config G f) (a : Directions G f) (i : Cell f) :=
  firstCut T.up R W a i - T.Mv R s V (i,true)

/-- The affine square term if selected (both p rows owned at their p anchor).
Use at W = replica ratio V. Incorporate channel weight only when applying
a composition (don't include twice). -/
def squareP (T : Tube G S) (R : ℕ) (s : ℝ) (V : Config G c) (W : Config G f) (a : Directions G f) (i : Cell f) :=
  ‖affF0 T R s V W a i‖^2 / 2+‖affF1 T R s V W a i‖^2 /2

def squareQ (T : Tube G S) (R : ℕ) (s : ℝ) (V : Config G c) (W : Config G f)
    (k : S.Choices) (a : Directions G f) (i : Bond c) :=
  ‖(Z S (S.prediction W k) V i - Real.sqrt S.kernel.penalty • qVar S W i k a)-T.Mw R s V i‖^2/2

private lemma sum_charge {F : ℕ → G.Color} {A h : ℝ} {f : ℕ → ℝ} (H : SumBudget f A) (hx : ∀ i, ‖F i‖ ≤ f i*h) (he : 0≤h) :
    Summable F ∧ ‖∑' i, F i‖ ≤ A*h := by
  have hq := H.2.1.mul_right h
  have hm := hq.of_nonneg_of_le (fun i => norm_nonneg _) hx
  refine ⟨hm.of_norm,(norm_tsum_le_tsum_norm hm).trans ((hm.tsum_le_tsum hx hq).trans ?_)⟩
  rw [tsum_mul_right]; gcongr; exact H.2.2

/-- Pay affine-row mismatch on its actual formula-length tests. -/
private lemma first_estimate (P : PathData G) {σ C Λ : ℝ} {c : Clip} (hP : P.Bounds c σ C Λ)
    (U W : Config G f) (a : Directions G f) (i : Cell f) (R : ℕ) (D h : ℝ) (hD : 0<D) (hh : 0≤h)
    (H : ∀ j, (P.row i.2 j).2.length ≤ R →
      let s := (P.row i.2 j).2
      let p := Work.F03.slotFace s i.1
      (∀ y : Bond f, y.1∈ (visits i.1 s.walk).toFinset → G.chord (U y*(W y)⁻¹)≤h) ∧
      ‖firstFace W a p‖≤ D*h ∧ ‖G.curvature (faceValue U p)-firstFace W a p‖ ≤ D*h^2) :
    Summable (perCharge P R W a i) ∧
    ‖firstCut P R W a i‖ ≤ C*(D*h) ∧
    ‖shorten P R 1 U i-firstCut P R W a i‖ ≤
      C*(D*(1+2*G.colorScale*(R:ℝ))*h^2) := by
  let C0 := G.colorScale
  have h0 := G.colorScale_pos
  have hC := hP.rows i.2
  let b j := ‖(P.row i.2 j).1‖ * Real.exp (σ*(P.row i.2 j).2.length)
  have hc : SumBudget b C := hC
  have hz j : ‖(P.row i.2 j).1‖ ≤ b j := le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (by have := hP.width; positivity))
  let M j := perCharge P R W a i j
  have hd j : ‖M j‖ ≤ b j*(D*h) := by
    unfold M perCharge firstSlot; dsimp only; split
    next hi => rw [norm_smul,G.norm_adjoint]; exact mul_le_mul (hz j) (H j hi).2.1 (norm_nonneg _) (hc.1 j)
    next hi => rw [norm_zero]; exact mul_nonneg (hc.1 j) (by positivity)
  let Y := D*(1+2*G.colorScale*(R:ℝ))*h^2
  have hY : 0≤Y := by unfold Y; positivity
  have ha j : ‖shortenTerm P R 1 U i j-M j‖ ≤ b j*Y := by
    unfold shortenTerm M perCharge firstSlot; dsimp only; simp only [mul_one]; split
    next hi =>
      obtain ⟨h1,h2,h3⟩ := H j hi
      rw [PathData.ellTerms, Work.F03.atSite_path, ← smul_sub, norm_smul]
      apply mul_le_mul (hz j) _ (norm_nonneg _) (hc.1 j)
      let S := (P.row i.2 j).2
      let x := Work.F03.slotFace S i.1
      let u := travel U i.1 S.walk; let w := travel W i.1 S.walk; let F := firstFace W a x
      let X := G.curvature (faceValue U x)
      have hr := travel_bound h _ _ _ _ h1
      change G.chord (u*w⁻¹)≤(S.walk.length:ℝ)*h at hr
      have he : (S.walk.length:ℝ) ≤ R := by
        have ht : S.walk.length ≤ S.length := by unfold Slot.length; omega
        exact_mod_cast ht.trans hi
      change ‖G.adjoint u X-G.adjoint w F‖ ≤ Y
      have hw := (ad_change F u w).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (hr.trans (mul_le_mul_of_nonneg_right he hh)) (by positivity)) h2 (norm_nonneg _)
          (show 0≤2*G.colorScale*(R*h) by positivity))
      apply (norm_sub_le_norm_sub_add_norm_sub _ (G.adjoint u F) _).trans
      rw [← map_sub,G.norm_adjoint]; apply (add_le_add h3 hw).trans_eq; unfold Y; ring
    next _ => rw [sub_zero,norm_zero]; exact mul_nonneg (hc.1 j) hY
  obtain ⟨hs,hm⟩ := sum_charge hc hd (mul_nonneg hD.le hh)
  refine ⟨hs,hm,?_⟩
  unfold shorten firstCut; rw [← (shorten_summable _ _ hP _ _ _).tsum_sub hs]
  exact (sum_charge hc ha hY).2

private lemma dominates (x y z : G.Color) {D E : ℝ} (h : ‖y‖ ≤ D) (hh : ‖z‖ ≤ D) (he : ‖x-y‖ ≤ E) :
    -(2*D*E) ≤ ‖x-z‖^2/2-‖y-z‖^2/2 := by
  have hi : ‖y-z‖ ≤ 2*D := (norm_sub_le ..).trans ((add_le_add h hh).trans_eq (by ring))
  have hE : 0 ≤ E := (norm_nonneg _).trans he
  rcases le_total ‖x-z‖ ‖y-z‖ with ht|ht
  · have hu : ‖y-z‖-‖x-z‖ ≤ E := by
      have hg := norm_sub_le_norm_sub_add_norm_sub y x z; rw [norm_sub_rev y x] at hg; linarith
    nlinarith only [mul_le_mul hu (show ‖y-z‖+‖x-z‖ ≤ 4*D by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _)) hE]
  have hp : ‖y-z‖^2 ≤ ‖x-z‖^2 := pow_le_pow_left₀ (norm_nonneg _) ht _
  nlinarith only [hp,hE,h,norm_nonneg y]

private lemma law (a : ℝ) (x y : G.Color) (h : ‖x‖ ≤ a) :
    ‖x-y‖^2/2 ≤ a^2/2+(‖y‖^2/2-inner ℝ y x) := by rw [norm_sub_sq_real,real_inner_comm]; nlinarith [norm_nonneg x]

lemma bond_square (T : Tube G S) (R : ℕ) (t : ℝ) (V : Config G c) (U W : Config G f) (a : Directions G f)
    (k : S.Choices) (i : Bond c)
    (C h : ℝ) (hC : 0<C) (hh : 0≤h)
    (hx : ‖T.Mw R t V i‖ ≤ C*h)
    (he : let X := Z S (S.prediction W k) V i
          let y := Real.sqrt S.kernel.penalty • qVar S W i k a
          ‖Z S (S.prediction U k) V i - (X-y)‖ ≤ C*h^2 ∧ ‖X‖ ≤ C*h ∧ ‖y‖ ≤ C*h) :
    -(4*C^2*h^3) ≤ T.workI R (S.prediction U k) V t i-squareQ T R t V W k a i := by
  obtain ⟨he,hz,hy⟩ := he
  let X := Z S (S.prediction U k) V i; let Y := Z S (S.prediction W k) V i-Real.sqrt S.kernel.penalty • qVar S W i k a
  let α := S.kernel.penalty
  let M := T.Mw R t V i
  let r := wire (S.prediction U k) V i
  have hY : ‖Y‖ ≤ 2*(C*h) := (norm_sub_le ..).trans ((add_le_add hz hy).trans_eq (by ring))
  have hM : ‖M‖ ≤ 2*(C*h) := hx.trans (by nlinarith)
  have hw := dominates X Y M hY hM he
  let K := Real.sqrt α
  have hk : 0≤K := Real.sqrt_nonneg _
  have hL : ‖X‖ ≤ K*r := by unfold X K α Z; rw [norm_smul,Real.norm_of_nonneg hk]; exact mul_le_mul_of_nonneg_left (G.curvature_norm _) hk
  have hS := law _ _ M hL
  rw [mul_pow,show K^2=α from Real.sq_sqrt S.kernel.penalty_pos.le] at hS
  change _ ≤ (α*r^2/2+(‖M‖^2/2-inner ℝ M X)) - ‖Y-M‖^2/2
  linarith only [hw,hS]

/-- All needed cut-path responses through actual paths (slot length includes the curvature
plaquette). Remaining shift cost measured on literal `Mv` including the thinned
physical clip data. Never evaluate selector of interest as smooth. -/
lemma fine_squares {σ C Λ : ℝ} (T : Tube G S) (hT : T.up.Bounds T.high σ C Λ)
    (R : ℕ) (t s : ℝ) (V : Config G c) (U W : Config G f) (a : Directions G f) (i : Cell f)
    (ht : toll U i ≤ t) (hk : PathData.kept T.high t i.1 U)
    (B h : ℝ) (hB : 0<B) (hh : 0≤h)
    (hr : ∀ j : Bool, ‖T.Mv R s V (i,j)‖ ≤ B*h)
    (he : ‖firstFace W a i‖≤ B*h ∧ ‖G.curvature (faceValue U i)-firstFace W a i‖ ≤ B*h^2)
    (H : ∀ j, (T.up.row i.2 j).2.length ≤ R →
      let s := (T.up.row i.2 j).2; let p := Work.F03.slotFace s i.1
      (∀ y : Bond f, y.1∈(visits i.1 s.walk).toFinset → G.chord (U y*(W y)⁻¹)≤h) ∧
      ‖firstFace W a p‖≤ B*h ∧ ‖G.curvature (faceValue U p)-firstFace W a p‖ ≤ B*h^2) :
    let d := Real.sqrt T.high.direct
    let m := d+C+1
    let p := 1+2*G.colorScale*(R:ℝ)
    Summable (perCharge T.up R W a i) ∧ -(4*(m*B)^2*p*h^3) ≤ T.workF R U V t s i-squareP T R s V W a i := by
  intro d m p
  obtain ⟨hq,H0,H1⟩ := first_estimate T.up hT U W a i R B h hB hh H
  refine ⟨hq,?_⟩
  let X0 := shoot T.high U i; let X1 := shorten T.up R 1 U i
  let Y0 := d • firstFace W a i; let Y1 := firstCut T.up R W a i
  let u := T.Mv R s V (i,false); let v := T.Mv R s V (i,true)
  let l := toll U i
  have hd := T.high.quadratic_pos
  have hd0 : 0≤d := Real.sqrt_nonneg _
  have hl : ‖X0‖ ≤ d*l := by unfold X0 shoot; rw [norm_smul,Real.norm_of_nonneg hd0]; exact mul_le_mul_of_nonneg_left (G.curvature_norm _) hd0
  have hC : 0≤C := (tsum_nonneg (hT.rows i.2).1).trans (hT.rows i.2).2.2
  have hm : d≤m ∧ C≤m ∧ 1≤m := by unfold m; constructor <;> [linarith; constructor <;> linarith]
  have hm' : 0<m := zero_lt_one.trans_le hm.2.2
  have hp : 1≤p := by unfold p; have := G.colorScale_pos; linarith [mul_nonneg (show 0≤2*G.colorScale by positivity) (Nat.cast_nonneg (α:=ℝ) R)]
  let y := m*B*h; let b := m*B*p*h^2
  have hy : B*h ≤ y := by unfold y; rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) hm.2.2
  have hz (a : ℝ) (ha : a ≤ m) : a*(B*h) ≤ y := by unfold y; rw [mul_assoc]; exact mul_le_mul_of_nonneg_right ha (by positivity)
  have hV : ‖Y0‖ ≤ y := by
    unfold Y0; rw [norm_smul,Real.norm_of_nonneg hd0]; exact (mul_le_mul_of_nonneg_left he.1 hd0).trans (hz d hm.1)
  have hw0 : ‖X0-Y0‖ ≤ b := by
    unfold X0 shoot Y0; change ‖d • _ - d • _‖ ≤ _; rw [← smul_sub,norm_smul,Real.norm_of_nonneg hd0]
    apply (mul_le_mul_of_nonneg_left he.2 hd0).trans
    unfold b; nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hm.1.trans
      (le_mul_of_one_le_right hm'.le hp)) hB.le) (sq_nonneg h)]
  have hN0 := dominates X0 Y0 u hV ((hr false).trans hy) hw0
  have hS0 := law (d*l) X0 u hl
  have hS1 := law ‖X1‖ X1 v le_rfl
  have hJ : ‖X1-Y1‖ ≤ b := by
    apply H1.trans
    unfold b p; rw [← mul_assoc,← mul_assoc]
    have hh := mul_le_mul_of_nonneg_right hm.2.1 (show 0 ≤ B*(1+2*G.colorScale*(R:ℝ))*h^2 by have := G.colorScale_pos; positivity)
    linarith only [hh]
  have hN1 := dominates X1 Y1 v (H0.trans (hz C hm.2.1)) ((hr true).trans hy) hJ
  unfold squareP affF0 affF1 workF; rw [Fintype.sum_bool,crown,trunk,if_pos hk,PathData.clipped,if_pos (show G.chord (faceValue U i) ≤ t from ht)]
  unfold Xf plotted; simp only [Bool.false_eq_true,↓reduceIte]
  change _≤((‖X1‖^2/2+T.high.direct*l^2/2)+((‖v‖^2/2-inner ℝ v X1)+(‖u‖^2/2-inner ℝ u X0)))-
    (‖Y0-u‖^2/2+‖Y1-v‖^2/2)
  rw [mul_pow,show d^2=T.high.direct from Real.sq_sqrt hd.le] at hS0
  unfold y b at *; linarith only [hS0,hS1,hN0,hN1]
end YM.SectorNext.Remainder.Affine
