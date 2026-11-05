import YM.Contacts.Layers.Overrides

/-!
# Testing approximations against an entire orbit of detectors

On the fixed horizon lists; growth (when used) happens only after this prescription is fixed.
Tests may run on compact/tie configurations within their separated domains. Approximants need only fit these *same* apertures at these readings. No fit through a distance bounded in units of a moving `u` log-rate layer.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Layers
open Function Filter Set Metric MeasureTheory Table Spec OPE
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {C : Family G} {S : Table C.book} {I J W : Type} [Fintype I] [Fintype J]
variable {F : Extraction.Order} {Z : Final C F S} {M : Devices Z.sector.derivatives}
variable {φ : Filter W} {T : W → ℝ} {c d r s u v a : ℝ}
variable {x : W → E4} {A B : Set (W → E4)}
variable {X : W→ I→E4} {Y : W→ J→ E4} {σ : W → Ortho}
local notation "D" => M.basis
local notation "R" => M.rotation
local notation "TK" => C.book.Token
local notation "EP" => W → Expression Z.sector.derivatives
variable {e f : W→ Expression Z.sector.derivatives}

-- collars
variable {d' : ℕ}
local notation "O" d => closedBall (0:E4) (M.aperture d)
local notation "SE" i => (shiftExpr (-(x i)) (e i))
def Fits (M : Devices Z.sector.derivatives) (φ : Filter W) (d : ℕ) (x : W→ E4) (A : Set (W → E4)) := ∀ y∈A,∀ᶠ i in φ, ‖y i-x i‖ ≤ M.clearance d
lemma Fits.suffices' (h : Fits M φ d' x A) {w : ℕ} (hp : w ≤ d') : ∀ y∈A,∀ᶠ i in φ, ‖y i - x i‖≤ M.aperture w:= fun y hy=> (h y hy).mono fun _ hi=> (hi.trans (M.antitone_clearance hp)).trans (M.clearance_le _)
lemma shift_support (x : E4) (E : Expression Z.sector.derivatives) (h : E∈ supportedAt (closedBall x r)) : shiftExpr (-x) E∈ supportedAt (closedBall 0 r) := by
  unfold supportedAt at h; induction h using Algebra.adjoin_induction with
  | mem y hy=> obtain ⟨x,hx,j,rfl⟩:= hy; rw [shift_unit]; exact unit_supportedAt _ _ (by simpa [Metric.mem_closedBall,dist_eq_norm,sub_eq_add_neg] using hx)
  | algebraMap x => simp only [AlgHom.commutes]; exact (supportedAt _).algebraMap_mem _
  | add _ _ _ _ hx hy=> rw [map_add]; exact (supportedAt _).add_mem hx hy
  | mul _ _ _ _ hx hy=> rw [map_mul]; exact (supportedAt _).mul_mem hx hy
lemma Fine.fit_shift (hf : Fine M φ T A s c e) (hc : Fits M φ d' x A) {w : ℕ} (hp : w ≤ d') : ∀ᶠ i in φ, shiftExpr (-(x i)) (e i) ∈ supportedAt (O w) := by
  refine (hf.fits (U:=fun i=>closedBall (x i) (M.aperture w)) (fun y hy=>?_)).mono fun i hi=> shift_support _ _ hi -- hi infer
  filter_upwards [hc.suffices' hp y hy] with i hi using (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hi))

variable (hT : Tendsto T φ atTop)

include hT
lemma tiny_rate (a : ℝ) (ha :0<a) (hs : 0 < s) : ∀ᶠ i in φ, Real.exp (-s*T i)<a:= (Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (by linarith : -s<0) hT)).eventually (gt_mem_nhds ha)

lemma rotation_rate {s : W → Ortho} (v : S.Field d') : RateLE φ T (fun i=> M.rotation.act d' (s i) v) 0 := by
  obtain ⟨K,hK⟩:= isCompact_univ.exists_bound_of_continuousOn (M.laws.spin d' v).continuousOn
  exact RateLE.absBound K hT (Eventually.of_forall fun i=> hK (s i) (Set.mem_univ _))
lemma act_any {f : W→ S.Field d'} (hf : RateLE φ T f c) (s : W→ Ortho) : RateLE φ T (fun i=> M.rotation.act d' (s i) (f i)) c := by
  conv => arg 3; intro i; rw [← (M.coherent d').rebuilds (f i),map_sum]; simp only [map_smul]
  refine RateLE.sum hT (fun j _=>?_)
  exact ((rate_linear (LinearMap.toContinuousLinearMap (M.basis.test j d')) hT hf).smul (rotation_rate (M:=M) (s:=s) hT _)).mono (add_zero c|>.le)

omit hT in
lemma fn_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Ortho → W → E}
    (h : ∀ s' : W→ Ortho, RateLE φ T (fun i=> f (s' i) i) c) : RateLE φ T (fun i=> ∫ s:Ortho, f s i ∂averageO) c:= by
  intro v hv; filter_upwards [universalize (p:=fun i s=> ‖f s i‖ ≤ Real.exp (v*T i)) (fun s=> h s v hv)] with i hi
  exact (norm_integral_le_of_norm_le_const (Eventually.of_forall hi)).trans (by simp)

omit hT in
lemma fn_star {f : W→ℂ} (h : RateLE φ T f c) : RateLE φ T (fun i=> star (f i)) c:= h.transfer (Eventually.of_forall fun i=>by simp)
lemma fn_real {f : W → S.Field d'} (h : RateLE φ T f c) : RateLE φ T (fun i=>M.conjugation d' (f i)) c:=
   ((RateLE.const ‖M.conjugation d'‖ hT).bil h (Eventually.of_forall fun i=> (M.conjugation d').le_opNorm (f i) |>.trans (by change _ ≤ ‖‖M.conjugation d'‖‖ * ‖f i‖; exact mul_le_mul_of_nonneg_right (Real.le_norm_self _) (norm_nonneg _)))).mono (zero_add c|>.le)
omit [Fintype I] hT in
lemma kept_single {i j:I} (h : Kept φ T s X) (hi : i≠j) : Cross φ T s {fun t=> X t i} {fun t=> X t j}:= by
  intro x hx y hy b hb; have hh:= Set.mem_singleton_iff.mp hx; have hf:=Set.mem_singleton_iff.mp hy; subst x y
  filter_upwards [h b hb] with t h a c using h i j hi

lemma Fine.group (d : I→ℕ) {p : ∀ i:I, W → S.Field (d i)} {a : I→ℝ} (h : Kept φ T s X)
    (ha : carries A X)(hf : ∀ i, RateLE φ T (p i) (a i - (d i : ℝ)*s)) : Fine M φ T A s (∑ i:I,a i) (fun t=>∏ i:I, insertField M.basis (X t i) (d i) (p i t)):= by
  have he:= Fine.product (M:=M) hT (p:=Finset.univ) (A':=fun j=>{fun t=>X t j}) (fun j _=> Fine.field hT (Set.mem_singleton _) (hf j)) (fun j _ k _ hk=> kept_single h hk)
  refine Fine.germ (he.enlarge (fun y hy=>?_)) ?_
  · obtain ⟨j,hj,hk⟩:= Set.mem_iUnion₂.mp hy; exact Set.mem_singleton_iff.mp hk ▸ ha j
  exact Eventually.of_forall fun t=> Finset.prod_apply ..

variable (M)
variable (p : Exterior C.book)
def placements (p : Exterior C.book) (s : Ortho) (x : E4) (i : Fin p.n) := Ortho.move s (bearing p i)+x
lemma rotating_kept (σ : W → Ortho) (x : W→ E4) : Kept φ T 0 (fun t=> placements p (σ t) (x t)) := by
  intro v hv
  have hf : ∀ (i j: Fin p.n), i≠j → ∀ᶠ t in φ, Real.exp (-v*T t)< ‖placements p (σ t) (x t) i-placements p (σ t) (x t) j‖:= by
    intro i j hj; unfold placements; simp_rw [add_sub_add_right_eq_sub,← Ortho.motion_at,← map_sub,LinearIsometryEquiv.norm_map]; exact tiny_rate hT _ (norm_pos_iff.mpr (sub_ne_zero.mpr ((beside_distinct.mp (bearing_clear p)).2.1.ne hj))) hv
  filter_upwards [eventually_all.mpr (fun i:Fin p.n=> eventually_all.mpr (fun j:Fin p.n=> (by
     by_cases h:i=j
     · exact Eventually.of_forall (p:=fun t=> i≠j→ Real.exp (-v*T t) < ‖placements p (σ t) (x t) i-placements p (σ t) (x t) j‖) fun _ h'=> (h' h).elim
     exact (hf i j h).mono fun t ht _=> ht)))] with t ht using ht
lemma rotating_clear {w : ℕ} (hc : ∀ y∈A,∀ᶠ i in φ,‖y i-x i‖≤ M.aperture w) (p : (M.tests w).probes) (σ : W→Ortho) : Cross φ T 0 A (pack (fun t=> placements p.val (σ t) (x t))) :=by
  rintro y hy z ⟨j,rfl⟩ a ha
  filter_upwards [tiny_rate hT _ (M.aperture_pos w) ha, hc y hy] with t ht h a' b
  change _ < ‖y t - placements p.val _ _ _‖; have h1: ‖placements p.val (σ t) (x t) j-x t‖= ‖Ortho.move (σ t) (bearing p.val j)‖:= by unfold placements; simp
  linarith only [ht,h,h1, M.aperture_clears p (σ t) j, norm_sub_le_norm_sub_add_norm_sub (placements p.val (σ t) (x t) j) (y t) (x t), norm_sub_rev (placements p.val (σ t) (x t) j) (y t) ]

lemma rotation_bill (σ : W→Ortho) (x : W→ E4) (b : Bool) (hu : 0 ≤ u) : Fine M φ T (pack (fun t=> placements p (σ t) (x t))) u ((sigma p.letter:ℝ)*u)
    (fun i=> shiftExpr (x i) (turnExpr D R (σ i) (M.probeWord p b))) := by
  let q:= if b then C.book.conjugate ∘ p.letter else p.letter; let d(i):= (q i).1; have he : sigma p.letter= ∑ i, d i:= by unfold d q; cases b <;> rfl
  have hf(t) : shiftExpr (x t) (turnExpr D R (σ t) (M.probeWord p b))=∏ i, insertField D (placements p (σ t) (x t) i) (d i) (M.rotation.act (d i) (σ t) (S.project _ (q i).2)):=by
     change shiftExpr _ (turnExpr _ _ _ (∏ i, insertField _ _ (d i) (S.project _ (q i).2)))= _
     rw [map_prod,map_prod]; refine Finset.prod_congr rfl fun i _=>?_
     rw [turn_field D R M.laws M.hierarchy.laws.toSymmetric M.incl M.coherent,shift_field]; rfl
  simp_rw [hf,he]; rw [Nat.cast_sum, Finset.sum_mul]
  exact Fine.group hT d ((rotating_kept hT p σ x).mono hu) pack_carries (fun i=> RateLE.mono (rotation_rate (M:=M) (s:=σ) hT (S.project _ (q i).2)) (le_of_eq (sub_self _).symm))
omit hT in
def probeFee (n : ℕ) := ∑ i : (M.tests n).probes,(sigma i.val.letter:ℝ)

lemma survey_rate {w : ℕ} (p : (M.tests w).probes) (h : Against Z M φ T A s v c e)
    (hc : Fits M φ w x A) (hs : 0 ≤ s) (hv : 0 ≤ v) (b : Bool) (σ : W→ Ortho) : RateLE φ T (fun i=> M.survey (σ i) p b (shiftExpr (-(x i)) (e i))) (c+probeFee M w*v) := by
  let w'(i):= turnExpr D R (σ i) (M.probeWord p.val b)
  have he:= rotation_bill M hT p.val σ x b hv; have hp := h ((rotating_clear M hT (hc.suffices' le_rfl) p σ).mono hs) he (fun _=>none)
  refine (hp.mono (by apply add_le_add (le_refl c); apply mul_le_mul_of_nonneg_right _ hv; exact Finset.single_le_sum (f:=fun i : (M.tests w).probes=>(sigma i.val.letter:ℝ)) (by intros; positivity) (Finset.mem_univ p))).congr ?_
  filter_upwards with i; change readExpr D S (e i*shiftExpr (x i) (w' i))= readExpr D S (shiftExpr (-x i) (e i) * w' i)
  rw [← shift_read D S M.hierarchy (-x i) (e i*_),map_mul,shift_add,add_neg_cancel,shift_zero]

lemma Against.row {w : ℕ} (e : W→ Expression Z.sector.derivatives)
    (h : Against Z M φ T A s v c e) (hs : 0 ≤ s) (hv : 0 ≤ v) (hc : Fits M φ w x A) (hE : ∃ u, Fine M φ T A 1 u e) : RateLE φ T (fun i=> M.row (x i) w (e i)) (c+probeFee M w*v) := by
   let θ := M.tests w; let k:=c+probeFee M w*v; let y (b:Bool) (i:W) (s:Ortho):= θ.decode (fun j=> if b then star (M.survey s j b (shiftExpr (-(x i)) (e i))) else M.survey s j b (shiftExpr (-(x i)) (e i)))
   have hm (b : Bool) (σ : W→Ortho) : RateLE φ T (fun i=> M.rotation.act w (σ i) (y b i (σ i))) k := by
      apply act_any (M:=M) hT _; apply rate_linear (LinearMap.toContinuousLinearMap (M.tests w).decode) hT (f:=fun i j=> if b then star (M.survey (σ i) j b (shiftExpr (-(x i)) (e i))) else M.survey (σ i) j b (shiftExpr (-(x i)) (e i))); intro v hv'
      let f' i (j:(M.tests w).probes):=if b then star (M.survey (σ i) j b (shiftExpr (-(x i)) (e i))) else M.survey (σ i) j b (shiftExpr (-(x i)) (e i))
      have he(j:(M.tests w).probes):RateLE φ T (fun i=>f' i j) k:= by unfold f'; cases b; exact survey_rate M hT j h hc hs hv false σ; exact fn_star (survey_rate M hT j h hc hs hv true σ)
      filter_upwards [eventually_all.mpr fun j=> he j v hv'] with i hi using (pi_norm_le_iff_of_nonneg (Real.exp_nonneg (v*T i)) (x:=f' i)).mpr hi
   have he(b : Bool):= fn_integral (f:=fun s i=> M.rotation.act w s (y b i s)) (hm b); let f:=M.hierarchy.spin
   let g(i:W):= M.base w (shiftExpr (-(x i)) (e i))
   apply rate_linear (LinearMap.toContinuousLinearMap (M.splitting.top w)) hT (f:=g); refine RateLE.congr ((((RateLE.const ((2:ℂ)⁻¹) hT).smul ((he false).add (fn_real (M:=M) hT (he true)) hT)).mono (le_of_eq (zero_add k)))) ?_
   filter_upwards [hE.choose_spec.fit_shift hc le_rfl] with i hi using (M.base_survey w hi).symm
end YM.Contacts.Layers
