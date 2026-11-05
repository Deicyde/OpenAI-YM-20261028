import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Resolve

/-!
# Estimate real μ near stationary input alone (counting units)

Hold geometry decisions same. Need supply same H,F front to patch call (and
post-lattice visits). Algebra on counting Hessian: true selected form D,
`Dᵀ*priced`, not a different RScene. Uses column error and station cancellation
separately. Rate envelope feeds both flag guard and mean exponent probability.
No cut derivative-of-mean assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {ι κ : Type*}

lemma ticket_local [Fintype κ] (M : Matrix ι κ ℝ) (i : ι) {E K : ℝ} (h : ∑ j,|M i j| ≤ E)
    (v : κ → ℝ) (hp : ∀ j, M i j ≠ 0 → |v j| ≤ K) (hK : 0≤K) : |(M *ᵥ v) i| ≤ E*K := by
  unfold mulVec dotProduct; apply (abs_sum_le_sum_abs ..).trans
  refine le_trans (b:= (∑ j, |M i j|) * K) ?_ (mul_le_mul_of_nonneg_right h hK)
  rw [Finset.sum_mul]; apply sum_le_sum; intro j _; by_cases h : M i j=0
  · simp [h]
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hp _ h) (abs_nonneg _)

lemma intensive (X : Coat T F) (hp : P.Funds S T) (v : Directions G f) :
    X.plate *ᵥ stand v + X.linearBill= X.form.transpose *ᵥ stand (X.priced v) + X.sleepy *ᵥ stand v := by
  obtain ⟨N,W,H,-⟩ := hp.feeds
  rw [X.pricing H,Matrix.mulVec_add, plate, Matrix.add_mulVec,← Matrix.mulVec_mulVec]; unfold linearBill; abel

lemma coil (X : Coat T F) (v : Directions G f) (M : ℝ) (hn : ∀ e∈F.trunks, v e=0)
    (i : Tubular f G) (hh : ¬Inside (along S i) X.seeds (11*X.B))
    {L : Side} {η r Q Y} (h : Rotator P L η r Q Y X) (hM : 0≤M)
    (hg : ∀ p : Mention c f, separation (root S p) (along S i) ≤ X.B → ‖X.realPath p.1 p.2 v‖ ≤ M) :
    |(X.plate *ᵥ stand v + X.linearBill) i| ≤ Y*(scale*M) := by
  have hz : (X.sleepy *ᵥ stand v) i=0 := by
    have hv : 0<X.B := lt_of_lt_of_le (by norm_num) h.room.sight.1
    rw [sleepy_act]; split
    · rfl
    next ht =>
      by_cases he : i.1∈F.trunks
      · unfold stand; rw [hn i.1 he]; rfl
      exact (ht (far_active X.seeds F _ (clear hh (by change 10*X.B+1+separation (along S i) (along S i)≤11*X.B; rw [separation_self]; omega)) he)).elim
  rw [intensive X h.room.accepted, Pi.add_apply, hz,add_zero]
  have hk : 0 ≤ scale*M := mul_nonneg scale_pos.le hM
  apply ticket_local _ i (pure_pay h.matrix.2 h.full.hot.le _) _ _ hk
  intro j hj; unfold stand; apply (stand_cap ..).trans
  unfold priced; split
  next hh =>
    rw [norm_smul,Real.norm_of_nonneg scale_pos.le]
    exact mul_le_mul_of_nonneg_left (hg _ (by
      have hh : separation (root S j.1) (along S i) ≤ X.B/4 := le_of_not_gt (fun H => hj (X.plume h.room j i H))
      omega)) scale_pos.le
  next he => rwa [norm_zero]

lemma drift_point (X : Coat T F) (v : Directions G f) (i : Tubular f G) {M U : ℝ} (hm : ‖v‖ ≤ U)
    {L : Side} {η r Q Y} (h : Rotator P L η r Q Y X) (hM : 0≤M)
    (hg : ∀ j∈ X.shutter.take i, |(X.plate *ᵥ stand v+X.linearBill) j| ≤ M) :
    let m := tubularPrice G L
    |(X.driftM-stand v) i| ≤ payE η r Q m * M + scraps η r Q m X.B * U := by
  intro m; let t := stand v
  let A := X.plate; let b := X.linearBill; let P := X.kernelA; let E := X.shutter.error X.plate
  have he : E.transpose=P.transpose*A-1 := by
    unfold E error; rw [Matrix.transpose_sub,transpose_mul,X.toned,transpose_one]; rfl
  have hp : X.driftM-stand v= E.transpose *ᵥ t - P.transpose *ᵥ (A *ᵥ t + b) := by
    rw [he,Matrix.sub_mulVec,← Matrix.mulVec_mulVec,Matrix.one_mulVec,Matrix.mulVec_add]
    change -(P.transpose *ᵥ b)-t=_; abel
  rw [hp, Pi.sub_apply, abs_sub_comm]
  have hv := h.full.prices
  apply (abs_sub ..).trans
  refine add_le_add ?_ (invoice (h.scale.discrepancy X.shutter).2 hv.le i t (fun i =>
    (stand_cap i.2 (v i.1)).trans ((norm_le_pi_norm _ _).trans hm)) ((norm_nonneg _).trans hm))
  refine ticket_local _ i (pure_pay (h.scale.primal X.shutter).2 (by linarith) _) _ ?_ hM
  intro j hj
  apply hg; by_contra hs; exact hj (X.shutter.outside X.plate j i hs)

lemma hips (X : Coat T F) (u v : Directions G f) (p : Mention c f)
    (hi : X.selected p.1 (spot S p.2)) {U : ℝ} (hp : 0≤U) {L : Side} {η r Q Y}
    (h : Rotator P L η r Q Y X) (hv : ∀ i : Tubular f G, separation (root S p) (along S i) ≤ X.B →
      |stand u i - stand v i| ≤ U) : ‖X.realPath p.1 p.2 u-X.realPath p.1 p.2 v‖ ≤
        (Fintype.card G.ColorIndex:ℝ)* (scale⁻¹*(Y*U)) := by
  have ht (i : G.ColorIndex) : |(X.priced u p-X.priced v p) i| ≤ Y*U := by
    obtain ⟨Ω,T,H,-⟩ := h.room.accepted.feeds
    change |(stand (X.priced u)-stand (X.priced v)) (p,i)| ≤ _
    rw [X.pricing H u, pricing X H v,add_sub_add_left_eq_sub,← Matrix.mulVec_sub]
    refine ticket_local _ _ (pure_pay h.matrix.1 h.full.hot.le _) _ ?_ hp
    intro j hj
    have he : separation (root S p) (along S j) ≤ X.B/4 := le_of_not_gt (fun H => hj (X.plume h.room (p,i) j H))
    exact hv _ (by omega)
  refine color_cover (mul_nonneg (inv_nonneg.mpr scale_pos.le) (mul_nonneg h.signs.le hp)) _ (fun i => ?_)
  have hx := ht i
  unfold priced at hx; rw [if_pos hi,if_pos hi, ← smul_sub] at hx
  simp only [PiLp.smul_apply,smul_eq_mul,abs_mul,abs_of_pos scale_pos] at hx
  exact le_of_mul_le_mul_left (hx.trans_eq (mul_inv_cancel_left₀ scale_pos.ne' _ |>.symm)) scale_pos

theorem pressure_mean (P : Teller G) (D : Patch) (hd : D.Branches P.bind G) (L : Side) (η r Q Y : ℝ) (hP : Torch η r Q) :
    ∃ E : ℝ → ℝ, Rate G L (-1) E ∧ ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D →
    S.patch.L=L → Stamp T → ∀ (F : Forest S.ratio) (X : Coat T F), X.x=x → Rotator P L η r Q Y X → X.manifest →
      0 ≤ E x ∧ ∀ i : Mention c f, ¬ Inside (root S i) X.seeds (30*X.B) → ‖X.realPath i.1 i.2 X.μ‖ ≤ E x := by
  obtain ⟨w,hv,h⟩ := flattening P L
  obtain ⟨A,hA,hX⟩ := retreat P L D hd hv (h.mono fun _ he => he.1)
  let m := tubularPrice G L
  obtain ⟨C,hC,H⟩ := spring_cap P
  let W x := C*w x
  let b x := Y*(scale*A x)
  let U x := payE η r Q m*b x+scraps η r Q m (radiusB x)*W x
  have hu : Rate G L (-1) U := by
    refine Rate.add (((hA.mul_left _).mul_left _).mul_left _) ?_
    convert (hP.physical G L (-(1/2)) m).mul (hv.mul_left C) using 1; norm_num
  let E x := A x+(Fintype.card G.ColorIndex:ℝ)*(scale⁻¹*(Y * U x))
  refine ⟨E,hA.add (((hu.mul_left Y).mul_left _).mul_left _),?_⟩
  filter_upwards [h,hX] with x hh hx c f S T hS hL hZ F X h' hr he
  subst x
  let k:=X.B
  have hp : 0 ≤ U X.x := by
    have hh := hh.1; have ht:=scale_pos; have hw:=hx.1; have hz:=hr.signs
    have hm : 0 ≤ scraps η r Q m (radiusB X.x) := hr.scale.heap _
    have hg : 0 ≤ payE η r Q m := hr.scale.disc; unfold U b W; positivity
  refine ⟨(by unfold E; have ht := scale_pos; have hy := hr.signs; have hh := hx.1; positivity),fun i hi=>?_⟩
  let o := root S i; have hB : 100≤ k := hr.room.sight.1
  have hV : Clean X.V X.x o (8*k+1) := (clean_far X.seeds X.V he hi).shrink (by
    change separation o o+_ ≤ 30*k; rw [separation_self]; omega)
  obtain ⟨z,g,hg,hb⟩ := hh.2 c f S T hL hr.room _ o (8*k) (by unfold k Coat.B; omega) hV
  let v := X.radiate z g
  have hk j (h : separation o (root S j)≤ 6*k) : ‖X.realPath j.1 j.2 v‖ ≤ A X.x :=
    hx.2 c f S T hS hL hr.room hZ F X rfl he j z g (clear hi (by unfold o k at *; omega))
      (hg.shrink (by unfold k at *; omega)) hb
  have hh : ‖v‖ ≤ W X.x := (spin_bounded ..).trans ((H S T hr.room.accepted F g).trans (mul_le_mul_of_nonneg_left hb hC.le))
  have hv j (he' : separation o (along S j) ≤ k) := X.drift_point v j hh hr (M:=b X.x)
    (by unfold b; have h := scale_pos; have hx:=hx.1; have hu := hr.signs; positivity) (fun p ht => by
      have hw : separation o (along S p) ≤ 3*k := (separation_triangle _ _ _).trans ((add_le_add he'
        ((separation_comm ..).trans_le (X.shutter.high p j ht))).trans (by unfold k; omega))
      refine X.coil v (A X.x) (X.trench z g) p (clear hi (by unfold o k at *; omega)) hr hx.1 fun i hh =>
        hk _ ((separation_triangle _ _ _).trans ((add_le_add hw ((separation_comm ..).trans_le hh)).trans (by unfold k; omega))))
  have hy : X.selected i.1 (spot S i.2) := by
    unfold selected addr; rw [← cost_is_here]; exact fun hz => hi (Corona.halo_mono (by omega) (by rfl) hz)
  have hw := X.hips X.μ v i hy hp hr (fun i he => hv i he)
  calc
    _ ≤ ‖X.realPath i.1 i.2 X.μ-X.realPath i.1 i.2 v‖ + ‖X.realPath i.1 i.2 v‖ := by
      simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub _ (X.realPath i.1 i.2 v) 0
    _ ≤ E X.x := (add_le_add hw (hk i (by unfold o; simp))).trans_eq (add_comm ..)
end YM.ConnectedActivityE6.Coat
