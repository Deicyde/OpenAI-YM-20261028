import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shutter


/-!
# Oriented stationary linear cancellation

Every rooted linear uncut F / noise row (paths still funded). Avoid
pretending mf entries isotropic or gauged at V. Use same input for all
channels; use algebra on full color bilinear and *separate* sworn metric
and floors from actual Horizon, arity. This is not a higher-jet comparison.
COPY tangent on the actual replica. `Stage` asks only linear-producer
quantities, no estimates on gas or Mayer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S}

/-- Literals from ONE chosen Horizon service. Statement existential so
alternative funded deployments can discharge without rerolling. -/
def Stamp (T : Tube G S) : Prop := ∃ B D : Bed, Towers.Diagonal S B D T.R ∧ Towers.Roll S B D T.R T.high T.low ∧
    Sworn B f G ∧ Sworn D c G ∧ Attached B T.up ∧ Attached D T.down ∧ ∃ a b : ℝ, Floor B T.high f a b ∧
    ∃ u v : ℝ, Floor D T.low c u v

def shifted (T : Tube G S) (F : Forest S.ratio) (x : LogField G c) :=
    stretch F (x, relative F (installed S.ratio T.R.A0) x)
def spring (T : Tube G S) (F : Forest S.ratio) (x : LogField G c) :=
    collect G (shifted T F x)-linearCopy S.ratio (collect G x)
lemma spring_ticks (F : Forest S.ratio) (x : LogField G c) (i : Bond f) :
    spring T F x i=if h : i∈F.trunks then 0 else relative F (installed S.ratio T.R.A0) x ⟨i,h⟩ := by
  rcases i with ⟨v,j⟩; simp [spring,collect,shifted,stretch, show axisEquiv.symm (coord j) = j from axisEquiv.symm_apply_apply j]

lemma linear_energy {B Z : Bed} (hT : Towers.Diagonal S B Z T.R) (F : Forest S.ratio) (x : LogField G c) :
    flatHess S B (x,shifted T F x) (x,shifted T F x)=gaugeFiscal Z x x := by
  let W := installed S.ratio T.R.A0
  let U := Precision.extracted S F W
  let M := B.metric.acts f; let N := Z.metric.acts c
  let a := relative (S:=S) F W x
  let z := (x, shifted T F x)
  let D := 1-probe S*U
  let v := parts G 1 x
  have he i : parts G 1 (residual S z) i = D *ᵥ (v i) := by
    change parts G 1 (crop F (x,a)) i = _
    rw [Work.F04.parts_crop, Work.F04.parts_stretch F W]
    unfold D; rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  have hk : K N = U.transpose*K M*U + S.kernel.penalty • (D.transpose*D)  := Eq.symm (Precision.action F W M N hT.trial)
  change gaugeFiscal B z.2 z.2+_=gaugeFiscal Z x x
  unfold gaugeFiscal; change _ + S.kernel.penalty*(∑ i, inner ℝ (residual S z i) (residual S z i)) = _
  rw [Work.F04.counting_inner, mul_sum, ← sum_add_distrib]; refine sum_congr rfl fun i _ => ?_
  rw [show parts G 1 z.2 i=U *ᵥ v i from Work.F04.parts_stretch F W x i,he, hk, Matrix.add_mulVec,dotProduct_add]
  change dotProduct (U *ᵥ v i) (_ *ᵥ (U *ᵥ v i)) + _ = dotProduct (v i) _ + _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ U.transpose, Matrix.vecMul_transpose,
    Matrix.smul_mulVec,dotProduct_smul, ← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec _ D.transpose, Matrix.vecMul_transpose]
  rfl

private lemma momentSquares {B : Bed} {Z : PathData G} {p σ C Λ a A} (h : Z.Bounds p σ C Λ) (hp : Attached B Z)
    (hk : Floor B p n a A) (x : LogField G n) : (∑ i, ‖xLin p Z x i‖^2)=gaugeFiscal B x x := by
  rw [Fintype.sum_prod_type, Work.F03.metric_pair B h hp x x hk]; refine sum_congr rfl fun i _ => ?_
  simp [xLin, norm_smul,mul_pow,Real.sq_sqrt p.quadratic_pos.le,add_comm]

private lemma noiseSquares (S : StepData c f) (x : LogField G c) (y : LogField G f) :
    (∑ i, ‖zLin S y x i‖^2) = S.kernel.penalty *
      ∑ i, inner ℝ (residual S (x,y) i) (residual S (x,y) i) := by
  rw [← Equiv.sum_comp (poleEquiv c) (fun i => inner ℝ (residual S (x,y) i) (residual S (x,y) i)),Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [zLin,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Real.sq_sqrt S.kernel.penalty_pos.le,
    real_inner_self_eq_norm_sq]; rfl

private lemma noisecash (V U) (h : P.Funds S T) (k : S.Choices) (s : Signed) :
    noiseTaylor S (pull s 0 (V:Config G c)) (pull s 0 U) (Oriented.choice s k) = noiseTaylor S V U k := by
  unfold noiseTaylor; congr 1
  conv_rhs => rw [← Equiv.sum_comp (StepData.sendBonds s 0)]
  apply sum_congr rfl; intro i _; rw [(Oriented.carry s (funds_branch h) k U).2]
  let Q := S.prediction U k
  have hh := Oriented.wire_pulled s Q V i
  apply mul_left_cancel₀ (show (2:ℝ) ≠ 0 by norm_num)
  rw [← G.chord_price, ← G.chord_price]; exact congr_arg (fun x : ℝ => x^2) hh

private lemma oriented_energy (h : P.Funds S T) (F : Forest S.ratio) {B D}
    (hv : Towers.Diagonal S B D T.R) (hB : Sworn B f G) (hD : Sworn D c G) (x : LogField G c) (s : Signed) :
    let a := pulled (shifted T F x) s; let b:=pulled x s
    flatHess S B (b,a) (b,a)=gaugeFiscal D b b := by
  intro a b
  let Y := shifted T F x
  have he := linear_energy hv F x
  let k : S.Choices := Classical.arbitrary _
  have ht := noise_limit (funds_branch h) k (x,Y)
  have hy := noise_limit (funds_branch h) (Oriented.choice s k) (b,a)
  have hz (t : ℝ) : noiseTaylor S (represent (t • b)) (represent (t • a)) (Oriented.choice s k)=
      noiseTaylor S (represent (t • x)) (represent (t • Y)) k := by
    rw [show a=pulled Y s from rfl,show b=pulled x s from rfl,← represent_pulled,← represent_pulled]
    exact noisecash _ _ h k s
  dsimp only at hy ht; simp_rw [hz] at hy
  have hp := tendsto_nhds_unique ht hy
  dsimp only [flatHess] at he ⊢
  rw [show gaugeFiscal B a a=_ from hB s Y Y, show gaugeFiscal D b b=_ from hD s x x]
  unfold Y at *; linarith only [hp,he]

lemma accords (h : P.Funds S T) (hg : Stamp T) (F : Forest S.ratio) (x : LogField G c) (s : Signed) :
    let a := Bid.pulled (shifted T F x) s; let b := Bid.pulled x s
    linearCost T a b = linearGuide T b := by
  intro a b
  obtain ⟨B,D,hD,hZ,hv,hw,hF,hf,d,e,h₁,f',u,h₂⟩ := hg
  obtain ⟨x',y',ha,hb⟩ := h.feeds
  rw [← h.high] at ha; rw [← h.low] at hb
  have he := oriented_energy h F hD hv hw x s
  let w := xLin T.low T.down b
  let u := xLin T.high T.up a
  let v := zLin S a b
  let U := zip (flatF T) w
  let V := zip (flatI T) w
  let N := zip (flatN T) w
  have hh i : N i=0 := zip_zero_N h b i
  have ht j : w j=unzip (flatF T) U j+unzip (flatI T) V j := by
    have h₃ := roll_d T hZ w j
    have hk : unzip (flatN T) N j=0 := sum_eq_zero fun i _ => by rw [hh]; exact map_zero _
    exact (sub_eq_zero.mp h₃).trans ((congr_arg (_ + ·) hk).trans (add_zero _))
  have hq j : w j=unzip (flatF T) u j+unzip (flatI T) v j :=
    (sub_eq_zero.mp (roll_l T hZ ha hb hF hf a b j)).symm
  let r := ∑ i, ‖w i‖^2
  have H : (∑ i, ‖u i‖^2)+∑ i, ‖v i‖^2=r := by
    unfold u v r w; rw [momentSquares ha hF h₁,momentSquares hb hf h₂,noiseSquares]
    exact he
  have HV : (∑ i, inner ℝ (U i) (U i)) + (∑ i, inner ℝ (V i) (V i))=r := by
    rw [arity (flatF T) U w,arity (flatI T) V w,← sum_add_distrib]
    simp_rw [← inner_add_right, ← ht, real_inner_self_eq_norm_sq]; rfl
  have HX : (∑ i, inner ℝ (U i) (u i))+(∑ i, inner ℝ (V i) (v i))=r := by
    rw [arity (flatF T) u w,arity (flatI T) v w,← sum_add_distrib]
    simp_rw [← inner_add_right,← hq,real_inner_self_eq_norm_sq]; rfl
  let E i := ‖linearGuide T b i-linearCost T a b i‖ ^ 2
  have hk : (∑ i, E i)=0 := by
    unfold E Rod
    rw [Fintype.sum_sum_type]
    change (∑ i, ‖U i - u i‖^2)+∑ i, ‖V i-v i‖^2=0
    simp_rw [real_inner_self_eq_norm_sq] at HV
    simp_rw [norm_sub_sq_real, sum_add_distrib,sum_sub_distrib,← mul_sum]
    linarith only [H,HX,HV]
  funext p
  have hu : E p≤0 := (single_le_sum (f:=E) (fun _ _ => sq_nonneg _) (mem_univ p)).trans_eq hk
  by_contra hx; exact hu.not_gt (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hx))) 2)
end YM.ConnectedActivityE6.SliceRows
