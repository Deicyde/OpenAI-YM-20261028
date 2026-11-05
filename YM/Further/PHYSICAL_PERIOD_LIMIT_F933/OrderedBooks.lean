import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Extra.WEAK_SCALING_ACTLAW.Criteria
import YM.Extra.WEAK_SCALING_ACTLAW.Producer
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Amend
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Post
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Suppression


/-!
# Return of continuum survey work to the finite ordered station port

Applying EXTRA WEAK only after reaching Hosted once does not require
redoing the corrected-sector jobs: can pay UVStress Stations from the
same-data comparison and the ordered point TEST limits at that stage.
The clamped chart reaching S's quotient can be sent back to actual
reference labels by a real-H section including unit, without assuming
any lifting norm estimate. Need also check that the precise `Station.paid`
upper (E.UV smear), simultaneous in arity and labels, sup-cost and
order sense, is inherited -- ties and volume included. This is not
deriving Stations from RPrep or from aligned data at some other C.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Upload
open Function Filter Set MeasureTheory Analysis Extraction Table Ward Climb Org Spec Next.UVStress
open Extra.WeakScaling renaming Stations → CutStations, FiniteCosts → Allocated, Supply → Payer
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {L : Register G} {S : Table L} {d D j : ℕ}

/-- Rep averaging with the actual register `space d` on the unit.
(Compare WEAK.Adjust.retraction for doing a *different* inclusion.) -/
lemma stable_rep (S : Table L) (H : S.Hierarchy) (d : ℕ) :
    ∃ Y : S.Field d →ₗ[ℂ] L.Ref d, (∀ v,S.project d (Y v)=v) ∧
      (∀ g v,Y (S.mirror H.spin d g v)=L.mirrorGroup d g (Y v)) ∧
      (∀ v, Y (S.conj H.spin d v)=star (Y v)) ∧ Y (S.unit d) = L.scalar d := by
  let k := L.scalar d; let z := k - S.representative d (S.unit d)
  let R := S.representative d + (Work.A15.front (S:=S) (n:=0) 0 Fin.elim0 d).smulRight z
  have hr v : S.project d (R v)=v := by
    simp only [R,z,k,LinearMap.add_apply,LinearMap.smulRight_apply,map_add,map_sub,map_smul,S.rep,
      show S.project d (L.scalar d) = S.unit d from rfl,sub_self,smul_zero,add_zero]
  have hR : R (S.unit d) = k := by simp [R,Extra.WeakScaling.unit_mean H,z]
  let Q := (Fintype.card Signed : ℂ)⁻¹ • ∑ s : Signed, (L.mirrorGroup d s⁻¹).comp (R.comp (S.mirror H.spin d s))
  have hc : (Fintype.card Signed : ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hq v : S.project d (Q v)=v := by
    simp only [Q, LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,map_smul,map_sum,
      ← S.mirror_project H.spin,hr, ← S.mirror_mul,inv_mul_cancel, S.mirror_one, Finset.sum_const,Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ,inv_smul_smul₀ hc]
  have hK : Q (S.unit d)=L.scalar d := by
    simp only [Q,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,S.mirror_unit,hR,k,L.mirror_scalar,Finset.sum_const,
      Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ,inv_smul_smul₀ hc]
  have hv g v : Q (S.mirror H.spin d g v)=L.mirrorGroup d g (Q v) := by
    simp only [Q,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,map_sum,map_smul]
    apply congr_arg (fun x : L.Ref d => (Fintype.card Signed : ℂ)⁻¹ • x)
    apply Fintype.sum_equiv (Equiv.mulRight g); intro s
    rw [show (Equiv.mulRight g) s=s*g from rfl, ← S.mirror_mul,← L.mirror_mul,mul_inv_rev,mul_inv_cancel_left]
  let B : S.Field d →ₗ[ℂ] L.Ref d := (L.bar d).comp (Q.comp (S.conj H.spin d))
  refine ⟨(2:ℂ)⁻¹ • (Q+B),fun v => ?_, fun g v => ?_, fun v => ?_,?_⟩
  · simp only [B,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.comp_apply,L.bar_apply,map_smul,map_add, ← S.conj_project H.spin,hq,S.reflect_star, ← two_smul ℂ]; simp
  · simp only [B, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, map_smul,map_add,L.bar_apply,S.mirror_star,hv,L.star_mirror]
  · simp only [B, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, star_smul,star_add,L.bar_apply,S.reflect_star,star_star]
    rw [add_comm]; congr 1; norm_num
  simp only [B,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.comp_apply,L.bar_apply,S.conj_unit,hK,L.bar_scalar,← two_smul ℂ]; simp
open Extra.WeakScaling
variable {S : Table C.book} {M n : ℕ} {Q : ℝ} {V : DiffPlan S} {W : DiffPlan (Free C)}
  {h : S.RealSpin} {H : (Free C).RealSpin} (b : Extra.WeakScaling.Curve V W h H M D Q)

/-- Order-zero pointwise estimates in station basis. Ties included on
window. -/
lemma estimated (hS : S.Hierarchy) (hV : V.Derivatives S) (hT : (Free C).Hierarchy) (hW : W.Derivatives (Free C))
    (R : ℝ) (hr : 1 ≤ R) (hR : R < Q) (hn : n ≤ M) (v : Fin n → (Free C).Tag) (hv : capped d v) (hd : d < D)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ x∈Scaling.window R n, ‖b.read v k x - disc v x‖ ≤ ε := by
  filter_upwards [b.tested hS hV hT hW hr hR hn _ hv 0 hd ε hε] with k hk x hx
  -- m=0 applying multilinear maps at empty basis (norm has exactly same value)
  specialize hk x hx
  rw [show iteratedFDeriv ℝ 0 (b.read v k) x - iteratedFDeriv ℝ 0 (disc v) x =
      iteratedFDeriv ℝ 0 (b.read v k - disc v) x from ?_,norm_iteratedFDeriv_zero] at hk
  · exact hk
  simp only [iteratedFDeriv_zero_eq_comp,comp_apply,map_sub,Pi.sub_apply]

/-- General finite tuple uniformization -- from absolute point price
per basis choice to a charge in the true station norms *uniform in
labels*. No finite test-net hypothesis for Continuum Quotients. -/
lemma operator {X : Type*} {s : Set X} {F : Fin n → Type*} [∀ i, NormedAddCommGroup (F i)]
    [∀ i, NormedSpace ℂ (F i)] [∀ i, FiniteDimensional ℂ (F i)] (M : ℕ → X → MultilinearMap ℂ F ℂ)
    (h : ∀ v : Code F, ∀ ε : ℝ, 0<ε → ∀ᶠ k : ℕ in atTop, ∀ x∈s, ‖M k x (combination F v)‖ ≤ ε)
    (e : ℝ) (he : 0<e) : ∀ᶠ k : ℕ in atTop, ∀ v : (i : Fin n) → F i, ∀ x∈s, ‖M k x v‖ ≤ e * (∏ i, ‖v i‖) := by
  classical
  let g (i) (j : Fin (Module.finrank ℂ (F i))) := (Module.finBasis ℂ (F i)).coord j |>.toContinuousLinearMap
  let A (v : Code F) := ∏ i, ‖g i (v i)‖
  let B := (∑ v : Code F,A v)
  have ha v : 0≤A v := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hb : 0≤B := Finset.sum_nonneg fun _ _ => ha _
  let ε := e/(1+B)
  have hp : 0<ε := by unfold ε; positivity
  have hz (v : Code F) (y : (i : Fin n) → F i) : ‖coords F v y‖ ≤ A v * ∏ i, ‖y i‖ := by
    unfold coords A; rw [Complex.norm_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => (g i (v i)).le_opNorm _
  filter_upwards [eventually_all.mpr fun v => h v ε hp] with k hk v x hx
  rw [basis_tuple F v (M k x)]
  apply (norm_sum_le ..).trans
  apply le_trans (Finset.sum_le_sum (f:=fun j => ‖coords F j v * M k x (combination F j)‖)
      (g:=fun j => (A j * ∏ i, ‖v i‖)* ε) (fun j _ => ?_)) ?_
  swap
  · rw [norm_mul]; exact mul_le_mul (hz ..) (hk j x hx) (norm_nonneg _) (mul_nonneg (ha j) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have ht : ε * (1+B) = e := div_mul_cancel₀ _ (by linarith : 1+B≠0)
  have hh : ε * B ≤ e := le_trans (mul_le_mul_of_nonneg_left (by linarith) hp.le) ht.le
  change B * _ * _ ≤ _
  rw [mul_right_comm B]
  exact mul_le_mul_of_nonneg_right (by rwa [mul_comm]) (Finset.prod_nonneg fun _ _ => norm_nonneg _)

lemma uniform_at (hS : S.Hierarchy) (hV : V.Derivatives S) (hT : (Free C).Hierarchy) (hW : W.Derivatives (Free C))
    (R : ℝ) (hr : 1 ≤ R) (hR : R < Q) (hn : n ≤ M) {c : Caps n} (hc : ∀ i, c i ≤ d) (hd : d < D)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ v : ∀ i : Fin n,(Free C).Field (c i), ∀ x∈Scaling.window R n,
      ‖b.read (fun i => ⟨c i,v i⟩) k x-disc (fun i => ⟨c i,v i⟩) x‖ ≤ ε * ∏ i, ‖v i‖ := by
  let A k (x : Points n) := matrixRead (forgetting b.X) k c (b.r k • x)-(Free C).classMoment (Free C) c x
  apply operator A (fun v ε hε => ?_) ε hε
  exact estimated b hS hV hT hW R hr hR hn (fun i => ⟨c i,combination (fun i => (Free C).Field (c i)) v i⟩) hc hd ε hε

lemma uniform_caps (hS : S.Hierarchy) (hV : V.Derivatives S) (hT : (Free C).Hierarchy) (hW : W.Derivatives (Free C))
    (R : ℝ) (hr : 1 ≤ R) (hR : R < Q) (hn : n ≤ M) (hd : d < D)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ v : Fin n → (Free C).Tag, capped d v → ∀ x∈Scaling.window R n,
      ‖b.read v k x-disc v x‖ ≤ ε*Station.charge v := by
  let F (c : Fin n → Fin (d+1)) : Caps n := fun i => (c i:ℕ)
  filter_upwards [eventually_all.mpr fun c => uniform_at b hS hV hT hW R hr hR hn (c:=F c) (fun i => Nat.le_of_lt_succ (c i).isLt) hd ε hε]
    with k hk v hv x hx
  let c (i : Fin n) : Fin (d+1) := ⟨(v i).1,Nat.lt_succ_of_le (hv i)⟩
  exact hk c (fun i => (v i).2) x hx

private lemma measure_price {n : ℕ} (s : Set (Points n)) (h : IsCompact s) (t : Test n) (ht : tsupport t ⊆ s)
    (Y : Points n → ℂ) {B c : ℝ} (hb : ∀ x, ‖t x‖ ≤ B) (hx : ∀ x∈s, ‖Y x‖ ≤ c) :
    ‖t.applyTo Y‖ ≤ volume.real s * (B*c) := by
  classical
  let f := s.indicator fun _ => B*c
  have hp : Integrable f := (integrable_indicator_iff h.measurableSet).mpr (integrableOn_const h.measure_lt_top.ne)
  rw [show volume.real s*(B*c)=∫ x,f x from ?_]
  · refine norm_integral_le_of_norm_le hp (Eventually.of_forall fun x => ?_)
    change ‖t x * Y x‖ ≤ _; rw [norm_mul]; by_cases H : x∈s
    · exact (mul_le_mul (hb x) (hx x H) (norm_nonneg _) ((norm_nonneg _).trans (hb x))).trans_eq (Set.indicator_of_mem H (fun _ => B*c)).symm
    rw [image_eq_zero_of_notMem_tsupport (show x∉tsupport t from fun h => H (ht h)),norm_zero,zero_mul]
    exact (Set.indicator_of_notMem H _).symm.le
  rw [show (∫ x,f x) = ∫ x in s, B*c from integral_indicator h.measurableSet, setIntegral_const, smul_eq_mul]

/-- All n positions priced at once. Multiplicative unit collapse and zero
label norms allowed. -/
lemma shell_price (hS : S.Hierarchy) (hV : V.Derivatives S) (hT : (Free C).Hierarchy) (hW : W.Derivatives (Free C))
    (R : ℝ) (hr : 1 ≤ R) (hR : R < Q) (hd : d < D)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in atTop,
      ∀ n ≤ M, ∀ (v : Fin n → (Free C).Tag), capped d v → ∀ (t : Test n), tsupport t ⊆ Scaling.window R n → ∀ c : ℝ, 0 < c →
        (∀ x, ‖t x‖ ≤ c) → ‖t.applyTo (b.read v k)-t.applyTo (disc v)‖ ≤ ε * Station.charge v * c := by
  let P (n) := volume.real (Scaling.window R n)
  let u n := ε/(P n+1)
  have hp n : 0 ≤ P n := MeasureTheory.measureReal_nonneg
  have hu n : 0 < u n := div_pos hε (by linarith [hp n])
  filter_upwards [eventually_all.mpr (fun n : Fin (M+1) => uniform_caps b hS hV hT hW R hr hR
      (n:=n.val) (Nat.le_of_lt_succ n.isLt) hd (u n) (hu n))] with k hk n hn v hv t ht c hc hZ
  have hf : ContinuousOn (b.read v k) (conf n) := (smoothZoom hS.smooth (routed (forgetting b.X) k ∘ v) (b.pos k)).continuousOn
  rw [← test_sub _ (disc v) hf (smoothDisc hT.smooth v).continuousOn t]
  have hv := hk (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (M+1)) v hv
  have hC : 0 ≤ Station.charge v := Finset.prod_nonneg fun _ _ => norm_nonneg _
  apply (measure_price _ (compact_window ..) t ht _ hZ hv).trans
  change P n * (c * (u n * Station.charge v)) ≤ _
  have hi : P n * u n ≤ ε := (mul_le_mul_of_nonneg_right (by linarith [hp n] : P n ≤ P n+1) (hu n).le).trans_eq
    (mul_div_cancel₀ _ (by linarith [hp n]))
  rw [show P n*(c*(u n*Station.charge v))=(P n*u n)*Station.charge v*c from by ring]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hC) hc.le

private abbrev reps (S : Table L) (H : S.Hierarchy) (d : ℕ) := (stable_rep S H d).choose
variable (hs : S.Hierarchy) (a e : ℕ)

def placing : Station C e :=
  { r := b.r a, rad:=b.pos _, atCut _ i := ((reps S hs i).comp (b.X a i).toLinearMap).toContinuousLinearMap }


lemma tendsto_paid {f : Extraction.Order} (H : f.Ordered C S) (v : Fin n → (Free C).Tag)
    (hv : capped e v) (t : Test n) : Tendsto (fun j : ℕ×ℕ => (placing b hs a e).paid v hv t j.1 j.2) f.fuse
      (𝓝 (t.applyTo (b.read v a))) := by
  let x : ∀ i : Fin n, C.book.Ref (v i).1 := fun i => reps S hs (v i).1 (b.X a (v i).1 (v i).2)
  let L (i : Fin n) := (⟨(v i).1,x i⟩ : C.book.Token)
  have hm := calibrated_smear H f.fuse (le_refl _) (d:=fun i => (v i).1) (dilate (b.pos a) t)
    (x:=x) (v:=fun _ => x) (fun _ => tendsto_const_nhds)
  unfold Table.integralOn at hm; rw [zoom_integral] at hm
  have he : routed (forgetting b.X) a ∘ v = S.classTokens ∘ L := funext fun i => by
    change (⟨(v i).1,b.X a (v i).fst (v i).snd⟩:S.Tag) = ⟨(v i).1,S.project _ (x i)⟩
    rw [(stable_rep S hs _).choose_spec.1]
  have hp y (hy : y∈conf n) : b.read v a y = S.value _ (b.r a • y) x := by
    change disc (routed (forgetting b.X) a ∘ v) _ = _
    rw [disc,he,S.at_project S hs.laws.toSymmetric (fun _=>le_rfl) (Work.A05.smul_conf (b.pos a) hy) L]; rfl
  have ht := t.apply_eq hp; rw [← ht] at hm
  exact hm

/-- Cash in the Graded b choice without post-L array bounds on these
new lifts; the *constant-in-(N,p)* fits can be used for Admissible at
the given regulator extraction (not promising actual λ-histories or
uniform k bounds for any such fitted Xi). Ergo may still demand
`CutStations` data including their own coef receipts upstream and just
extract the needed UV-Stress-facing station occupations again from the
common hierarchy. No paying the physical module twice. -/
lemma enough {f : Extraction.Order} (hp : f.Ordered C S) (hV : V.Derivatives S) (hT : (Free C).Hierarchy) (hW : W.Derivatives (Free C))
    (R : ℝ) (hr : 1 ≤ R) (hR : R < Q) (hd : e < D)
    (ε : ℝ) (hε : 0<ε) : ∀ᶠ k in atTop,(placing b hs k e).Admissible f hT.spin M R ε := by
  filter_upwards [b.graded,shell_price b hs hV hT hW R hr hR hd ε hε] with i hg hk
  let X := placing b hs i e
  have hg j (h : j ≤ D) := hg.1 j h
  let Y := fun j => (stable_rep S hs j).choose_spec
  refine ⟨⟨‖X.atCut (0,0)‖,Eventually.of_forall fun _ => Eventually.of_forall fun _ => le_rfl⟩,
    Eventually.of_forall fun _ => Eventually.of_forall fun _ => ?_,
    Eventually.of_forall fun _ => Eventually.of_forall fun _ => ?_,
    Eventually.of_forall fun _ => Eventually.of_forall fun _ => ?_, fun n hn hv x hx T hT hB η hη => ?_⟩
  · change reps S hs 0 (b.X i 0 _) = _
    rw [show b.X i 0 ((Bel C.book).unit 0)=_ from (hg 0 (Nat.zero_le _)).2.2]
    exact (Y 0).2.2.2
  · intro j y; have he := (hg j ((Nat.le_of_lt_succ j.isLt).trans hd.le)).2.1 y
    change reps S hs j (b.X i j ((Bel C.book).conj _ _ y)) = _
    change b.X i j ((Bel C.book).conj hT.spin j y) = S.conj hs.spin _ _ at he
    rw [he]; exact (Y j).2.2.1 _
  · intro j s y; have he := (hg j ((Nat.le_of_lt_succ j.isLt).trans hd.le)).1 s y
    change reps S hs j (b.X i j ((Bel C.book).mirror _ _ s y)) = _
    change b.X i j ((Bel C.book).mirror hT.spin j s y) = S.mirror hs.spin _ _ _ at he
    rw [he]; exact (Y j).2.1 _ _
  change ∀ᶠ j : ℕ × ℕ in f.fuse, ‖X.paid hn hv x j.1 j.2 - x.applyTo (disc hn)‖ ≤ ε*Station.charge hn*T + η
  exact ((show Tendsto (fun j : ℕ×ℕ => ‖X.paid hn hv x j.1 j.2 - x.applyTo (disc hn)‖) f.fuse _ from
      ((tendsto_paid b hs i e hp hn hv x).sub_const _).norm).eventually (ge_mem_nhds
      (show ‖x.applyTo (b.read hn i) - x.applyTo (disc hn)‖ < ε * Station.charge hn * T + η from (hk _ n hn hv x hx T hT hB).trans_lt (lt_add_of_pos_right _ hη))))


/-- Therefore one need only seek the more explicit `Allocated`
finite cost data (center/rooted and aligned moments with their grid
spacings/sublinear bills, no assumption of bounds on tested smears),
e.g., see `Extra.WeakScaling.Rooted`. Can choose them fairly early on
*any* inherited Seed or just at the Host on demand. This proves the
Stations input, even on the initial order of the common Host (using its
actual Ordered and Funding data to instantiate the Work producer after
refinements and then staying at the S obtained before those refinements).
Scopes are not to be weakened even only for finite numerical heights.
-/
theorem fair {f : Extraction.Order} (s : Seed C f S) (W : MaxwellData C)
    (hp : V.Inclusions S) (hh : V.Derivatives S) (H : Payer C f W.hT.spin) :
    Next.UVStress.Stations C f W.hT.spin := by
  constructor; intro D N R ε δ hR he hd
  obtain ⟨Q,hQ,⟨b⟩⟩ := weak_curve s W H N (D+1) R hR hp hh
  obtain ⟨k, hk, hy⟩ := ((enough b s.kernel D s.ordered hh W.hT W.lit.pales R hR hQ (Nat.lt_succ_self D) ε he).and
    (b.shrinks.eventually (ge_mem_nhds hd))).exists
  exact ⟨placing b s.kernel k D,hk,hy⟩
end YM.Further.PhysicalPeriodLimitF933.Upload
