import YM.AnalyticNext.QUARTIC_MATCH.Local.Direction
import YM.AnalyticNext.QUARTIC_MATCH.Local.Members
import YM.AnalyticNext.QUARTIC_MATCH.Local.Stipple


/-!
# Affording the real centered action jets

Linear in the cubic/quartic input path budgets before pairs. Call uniformly
before lengths. Upgrading path bill in the iteration deferred. No change to
common tags, using actual unmasked prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Local
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Centered
open Joint Estimate Estimate.Purse Estimate.Logfee Estimate.Depot BoxChain
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Budget
open Premium Evoke
open Green (wt)
variable {G : Gauge} {n l c f : Side} (S : StepData c f)

def assistance (l : Side) (R3 R4 : ℝ) := 1+R3/(l.val:ℝ)^2+R4/(l.val:ℝ)^4
lemma cost_support {R3 R4 : ℝ} {p : PathData G} {σ η D : ℝ} {j} (h : Rotate.Led p l j η σ D R3 R4) :
    1 ≤ assistance l R3 R4 := by
  have hb := h.three.fee; have hc := h.four.fee
  exact (le_add_of_nonneg_right (div_nonneg hb (sq_nonneg _))).trans (le_add_of_nonneg_right (div_nonneg hc (by positivity)))

def feeDown (G : Gauge) (n : ℕ) (η R s : ℝ) := overall s * Rotate.totalBill G η R n
lemma fee_paid (G : Gauge) (n : ℕ) (η R s : ℝ) : 0 < feeDown G n η R s :=
    mul_pos (zero_lt_one.trans_le (Premium.cover_ge _)) (Rotate.totalBill_pos ..)

lemma base_amount {ι : Type} [DecidableEq ι] {W : PathData G} {v : ι→Dir G f} {P : Purse ι (Site f)}
    {L : Side} {n : ℕ} {σ τ R R3 R4 K Λ M η u : ℝ} {p : Clip} (sx : Finset ι)
    (hx : sx.card ≤ n) (hg : W.Bounds p τ K Λ) (hp : Rotate.Led W L n η σ R R3 R4)
    (he : 0<η) (hP : tollRate P L η) (ht : P.cap=(L.val:ℝ)^2)
    (hb : Linkbill L P v) (hC : Plaque.BendBill L P v) (hR : 0 ≤ M) (hu : 0<u) (z : Site f) (hy : Stamp P sx L u M z) :
    M * ‖bill sx v (fun x => mainTerm p W (represent x)) 0‖ ≤ feeDown G n η R u * assistance L R3 R4 * P.target sx := by
  rw [show (fun x : Dir G f => mainTerm p W (represent x))=(fun a => ∑ i, Rotate.byStage p W i a) from funext (Rotate.unroll p W)]
  rw [sum_bill Finset.univ sx v (Rotate.byStage p W) 0 (fun i _ => Rotate.stage_rate hg ..)]
  exact (Premium.tariff (Rotate.tally hb hP he hC hx hg hp) ht hu hR z hy).trans_eq (by unfold feeDown assistance; field_simp)

lemma charged (a : S.Choices) (p : Clip) (W : PathData G) (z : JointSpace G c f) :
    cash S a p W z=mainTerm p W (represent z.2.1)+S.kernel.penalty*∑ y : Site c,∑ i : Axis, coins S a y i z := by rw [cash,groupEnergy,Fintype.sum_prod_type]; rfl

lemma awards (G : Gauge) (j m : ℕ) (η u D κ : ℝ) (he : 0<η) (hu : 0<u) (hκ : 0<κ) :
    ∃ C : ℝ,0≤C ∧ ∀ (c f : Side) (S : StepData c f) (p : Clip) (W : PathData G) (a : S.Choices) (σ τ K Λ R3 R4 : ℝ),
      S.patch.J=j → S.kernel.penalty=κ → S.patch.Branches S.kernel G → W.Bounds p τ K Λ → Rotate.Led W S.patch.L m η σ D R3 R4 →
      ∀ (ι : Type) [DecidableEq ι] (P : Purse ι (Site f)) (T : Finset ι) (v : ι→ JointSpace G c f), T.card ≤ m →
        P.cap=(S.patch.L.val:ℝ)^2 → tollRate P S.patch.L η → (∀ i,Presents S P i (v i)) →
        ∀ (z : Site c) (M : ℝ),0 ≤ M → Stamp P T S.patch.L u M (S.ratio.embed z) →
          M* |bill T v (cash S a p W) 0| ≤ C*assistance S.patch.L R3 R4 * P.target T := by
  obtain ⟨K,hK,H⟩ := Depot.pays G m j η he
  let C := feeDown G m η D u
  let R := κ*(overall u*(Fintype.card Axis*K))
  refine ⟨C+R,add_nonneg (fee_paid ..).le (mul_nonneg hκ.le (mul_nonneg (zero_le_one.trans (Premium.cover_ge u)) (by positivity))),?_⟩
  intro c f S p W a σ τ K' Λ R3 R4 hs hk hh hP hR ι _ P T v hm hv ht hy z M ha hx
  obtain ⟨h1,h2⟩ := Evoke.lays S P v hy
  let w := ∑ _i : Axis, K
  let d (x : Site c) (p : JointSpace G c f) := ∑ i, coins S a x i p
  have hd x : ContDiffAt ℝ ω (d x) 0 := ContDiffAt.sum fun i _ => Depot.coin_smooth S a hh x i
  let Q := Yard.cap S P
  have he' : Q.Jets T v d 0 w := Jets.allotted Finset.univ (fun i y => coins S a y i) (fun i _ y => Depot.coin_smooth S a hh y i)
    (fun i _ => H _ _ _ S a hs hh P v ht hv h1 T hm i)
  have hQ : Stamp Q T 1 u M z := by
    intro y
    have hh := hx (S.ratio.embed y); rw [show (S.patch.L.val:ℝ)=(S.ratio.count.val:ℝ) from rfl, accrual] at hh
    simpa only [Q, Yard.cap_price, PNat.val_ofNat, Nat.cast_one, div_one] using hh
  let b (x : Dir G f) := mainTerm p W (represent x)
  have hb : ContDiffAt ℝ ω b 0 := Work.F02.mainTerm_contDiffAt (A:=represent) hP (fun i => (represent_smooth ..).contDiffAt)
  let L : JointSpace G c f →L[ℝ] Dir G f := ContinuousLinearMap.fst ℝ (Dir G f) (LieSpin G c) ∘L ContinuousLinearMap.snd ℝ (Dir G c) _
  have hg : ContDiffAt ℝ ω (fun p => b (L p)) 0 := by
    apply ContDiffAt.comp (f:=L) (g:=b) _ _ L.contDiff.contDiffAt
    rw [map_zero]; exact hb
  let f₁ (p : JointSpace G c f) := ∑ i,d i p
  have hf₁ : ContDiffAt ℝ ω f₁ 0 := ContDiffAt.sum fun i _ => hd i
  rw [show cash S a p W=(fun p => b (L p)+(κ • f₁) p) from funext fun i => by rw [charged,hk]; rfl,
    plus_rate _ _ hg (by exact hf₁.const_smul κ), smul_price _ _ hf₁,
    show bill T v (fun y => b (L y)) 0=bill T (L ∘ v) b 0 from Depot.lin_rate L b v hb T,
    show bill T v f₁ 0 = ∑ x:Site c,bill T v (d x) 0 from sum_bill Finset.univ T v d 0 fun i _ => hd i]
  let t := assistance S.patch.L R3 R4
  apply (mul_le_mul_of_nonneg_left (abs_add_le ..) ha).trans
  rw [mul_add,smul_eq_mul, abs_mul,abs_of_nonneg hκ.le]
  have hb' := base_amount (v:=L ∘ v) T hm hP hR he ht hv h1.1 h2 ha hu (S.ratio.embed z) hx
  have hk := Premium.tariff he' (l:=1) (by norm_num [Q,Yard.cap]) hu ha z hQ
  rw [show w=(Fintype.card Axis:ℝ)*K by simp [w],show Q.target T=P.target T from rfl] at hk
  have heM : M * (κ * |∑ x,bill T v (d x) 0|) ≤ κ * (overall u * ((Fintype.card Axis*K)*P.target T)) := by
    rw [mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ hκ.le
    simpa using hk
  refine (add_le_add hb' heM).trans ?_
  change C*t*_+_ ≤ (C+R)*t*_
  apply (show _+_=C*t*(P.target T)+R*P.target T from by unfold R; ring).le.trans
  rw [add_mul,add_mul]; apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (show 0≤R from mul_nonneg hκ.le (mul_nonneg (zero_le_one.trans (Premium.cover_ge u)) (by positivity)))
    (cost_support hR)) (P.target_pos _)
end Budget
end YM.AnalyticNext.QuarticMatch.Local
