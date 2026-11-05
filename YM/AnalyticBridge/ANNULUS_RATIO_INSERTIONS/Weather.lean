import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Arc
import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Chord
import YM.Next.ROTATIONS.Response



/-!
# Some *actual* r4 receipts

Thus applies on the INLET ratio exponent on
orders 0 without ζ; do NOT assign these block coefficients
only the endpoints' data as supports: e.g.

C⁻¹ evaluates many other
positions, Shares/kernel uses them jointly with other labels too.

The
ancillary estimate here isolates the Gaussian-integration use of this
comparison, prices even arbitrary sublists of the actual blocks (color
sums at same two positions), without certifying support of the factors
*after* integration or hits on sites other than endpoints.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Prism.Breeze
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented 
open Tier Wisps Schur LocalJet Completion

open Arc
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure

section covers
variable {I : Type} [Fintype I] [DecidableEq I] {G : Gauge}

def shade (A : Gaussian.Table (I × G.ColorIndex)) (i : I × I) (z : Prices G I) : ℝ :=
  (∑ j:G.ColorIndex, ∑ l:G.ColorIndex, z (i.1,j)*(A (i.1,j) (i.2,l)*z (i.2,l)))/2

@[fun_prop] lemma measurable_shade (A : Gaussian.Table (I × G.ColorIndex)) (i : I × I) : Measurable (shade A i) := by unfold shade; fun_prop



private lemma pigment (z : Prices G I) (i : I) (j : G.ColorIndex) : |z (i,j)|^2 ≤ load z i := by
  unfold load; rw [EuclideanSpace.real_norm_sq_eq,sq_abs]
  change z (i,j)^2 ≤ ∑ u:G.ColorIndex,z (i,u)^2
  exact Finset.single_le_sum (f:=fun b:G.ColorIndex=>z (i,b)^2) (fun _ _=>sq_nonneg _) (Finset.mem_univ _)

private lemma younger (z : Prices G I) (i : I × I) {u v : G.ColorIndex} :
    |z (i.1,u)| * |z (i.2,v)| ≤ Arc.mast id i z := by
  unfold mast; dsimp only [id_eq]
  nlinarith only [pigment z i.1 u,pigment z i.2 v, sq_nonneg (|z (i.1,u)|-|z (i.2,v)|),load_nonneg z i.1, load_nonneg z i.2]

lemma shade_price (A : Gaussian.Table (I × G.ColorIndex)) (i : I × I) {D : ℝ} (hD : 0 ≤ D) (z : Prices G I)
    (h : ∀ a b:G.ColorIndex, |A (i.1,a) (i.2,b)| ≤ D) :
    |shade A i z| ≤ (Fintype.card G.ColorIndex:ℝ)^2 * D * Arc.mast id i z := by
  have ht (a b : G.ColorIndex) : |z (i.1,a)*(A (i.1,a) (i.2,b)*z (i.2,b))| ≤ D * Arc.mast id i z := by
    rw [abs_mul,abs_mul,mul_left_comm]; exact mul_le_mul (h a b) (younger z i) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hD
  have hz : 0≤ Arc.mast id i z := (zero_le_one.trans (mast_one ..))
  unfold shade; rw [abs_div,abs_of_nonneg (by norm_num : 0≤(2:ℝ))]
  refine (div_le_self (abs_nonneg _) (by norm_num)).trans ((Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum
    (g:=fun a => (Fintype.card G.ColorIndex:ℝ)*(D* Arc.mast id i z)) (fun a (_:a∈Finset.univ)=>(Finset.abs_sum_le_sum_abs ..).trans ?_)).trans_eq (by simp; ring)))
  exact (Finset.sum_le_sum (g:=fun b=> D * Arc.mast id i z) (fun b (_:b∈Finset.univ)=>ht a b)).trans (le_of_eq (by simp))

/-- Submission has both post-L rates. It depends only on height,
physical pair positions (and torus distances), independently of sector
information apart from expressing the endpoints, NOT asserting this is
the dependency of the matrix elements themselves. -/
def ebb (a v : ℝ) (r d : ℕ) := rate (-(a/4)) r * rate (-(v/4)) d

lemma ebb_nn (a v : ℝ) (r d : ℕ) : 0≤ebb a v r d := mul_nonneg (rate_pos ..).le (rate_pos ..).le



lemma rate_duel {a v D h : ℝ} {r y : ℕ} (hD : 0≤D) (he : |h| ≤ D*rate (-a) r)
    (hw : |h| ≤ 2*D*rate (-v) y) : |h| ≤ 2*D*(ebb a v r y)^2 := by
  unfold ebb rate; rw [← Real.exp_add, sq,← Real.exp_add, show -(a/4)*(r:ℝ)+-(v/4)*(y:ℝ) + (-(a/4)*(r:ℝ)+-(v/4)*(y:ℝ)) = -(a*(r:ℝ)+v*(y:ℝ))/2 by ring]
  by_cases hx : a*(r:ℝ) ≤ v*(y:ℝ)
  · apply hw.trans; unfold rate; gcongr; linarith
  apply he.trans; unfold rate
  refine mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by linarith)
  linarith

variable {c f : Side} (S : StepData c f)

def destination (A : Stores S) (F : Forest S.ratio) {x : ℝ} (i : Active A x F) : Site c := S.ratio.parent i.1.1.1

def colorInk (G : Gauge) (M : ℝ) := 1+ (Fintype.card G.ColorIndex : ℝ)^2 * (2*M)
lemma colorInk_one (G : Gauge) {M : ℝ} (hM : 0≤M) : 1≤ colorInk G M := le_add_of_nonneg_right (by positivity)

def salt (A : Stores S) (F : Forest S.ratio) (x : ℝ) (G : Gauge) (a v M : ℝ) (i : Active A x F × Active A x F) :=
  colorInk G M * ebb a v (radiusB x) (separation (destination S A F i.1) (destination S A F i.2))
lemma salt_nn (A : Stores S) (F : Forest S.ratio) (x : ℝ) (G : Gauge) (a v M : ℝ) (hM : 0≤M)
    (i : Active A x F × Active A x F) : 0≤salt S A F x G a v M i := by unfold salt; exact mul_nonneg (zero_le_one.trans (colorInk_one _ hM)) (ebb_nn ..)

lemma greet {v u a M x : ℝ} {T : Tube G S} (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c)
    (hM : 0≤M) (h : Specs x v u a M T A F k V) (i : Active A x F × Active A x F) (z : Prices G (Active A x F)) :
    let U:= Rows.gram T x V k (shots S x) A F
    let C:= fog A F T x V k
    |shade (C⁻¹-U) i z| ≤ salt S A F x G a v M i ^ 2 * Arc.mast id i z := by
  intro U C; obtain ⟨-, -, hL,-,-,-,hC,-,ht⟩:=h.tables
  let d:= separation (destination S A F i.1) (destination S A F i.2)
  have he (j l : G.ColorIndex) : |(C⁻¹-U) (i.1,j) (i.2,l)| ≤ 2*M*(ebb a v (radiusB x) d)^2 := by
    refine rate_duel hM ?_ ?_
    · have ht := ripple ht (i.1,j) (i.2,l); simp only [rate,zero_mul,Real.exp_zero,one_mul] at ht; exact ht
    have hi := ripple (pours_minus hC hL) (i.1,j) (i.2,l)
    change rate v d * _ ≤ M+M at hi
    have hh := mul_le_mul_of_nonneg_right hi (rate_pos (-v) d).le
    have hz : rate v d*rate (-v) d=1 := by unfold rate; rw [← Real.exp_add]; ring_nf; rw [Real.exp_zero]
    change rate v d * |(C⁻¹-U) (i.1,j) (i.2,l)| * rate (-v) d ≤ _ at hh
    rw [mul_right_comm, hz,one_mul] at hh; linarith only [hh]
  apply le_trans (shade_price (C⁻¹-U) i (by positivity) z he)
  set n : ℝ := ↑(Fintype.card G.ColorIndex)
  unfold salt
  set m := ebb a v (radiusB x) d
  refine mul_le_mul_of_nonneg_right ?_ (zero_le_one.trans (mast_one ..))
  rw [mul_pow]
  have hh : n^2*(2*M) ≤ colorInk G M^2 := by
    change n^2*(2*M) ≤ (1+n^2*(2*M))^2
    have hl : 0≤n^2*(2*M) := by positivity
    nlinarith
  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)
end covers

section counts
variable {G : Gauge} (Q : Patch) (v : ℝ)

def storm (Q : Patch) (v : ℝ) : ℝ := Tier.wealth v * (Fintype.card (Site Q.L)*Fintype.card Axis)
lemma storm_nn : 0 ≤ storm Q v := mul_nonneg (Tier.wealth_nn v) (by positivity)

private lemma counted {c f : Side} (S : StepData c f) (h : S.patch=Q) (o : Site c) (A : Stores S) (F : Forest S.ratio)
    (x : ℝ) (hv : 0 < v) : (∑ i:Active A x F, rate (-v) (separation o (destination S A F i))) ≤ storm Q v := by
  let R (i : Site c) := rate (-v) (separation o i)
  let P (i : Bond f) := R (S.ratio.parent i.1)
  let e (z : Active A x F) := z.val.val
  have he : Function.Injective e := fun _ _ t => Subtype.ext (Subtype.ext t)
  calc
    _ ≤ ∑ i : Bond f, P i := by
      change (∑ i:Active A x F,P (e i)) ≤ _
      rw [← Finset.sum_image (g:=e) (f:=P)]
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=> (rate_pos ..).le)
      exact fun _ _ _ _ => @he _ _
    _ = ((Fintype.card Axis:ℝ)*(Fintype.card (Site Q.L):ℝ)) * ∑ i:Site c,R i := by
      change (∑ i: Site f × Axis, _) = _
      rw [Fintype.sum_prod_type]; unfold P
      simp_rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum,Work.F01.sum_parent S.ratio R]
      have hh : Fintype.card (Site S.patch.L)= Fintype.card (Site Q.L) := by rw [h]
      change (Fintype.card Axis:ℝ)*((Fintype.card (Site S.patch.L):ℝ)*∑ i,R i)=_
      rw [hh,mul_assoc]
    _ ≤ storm Q v := by
      have he : ∑ i:Site c,R i ≤ Tier.wealth v := by unfold R; simp_rw [separation_comm o]; exact Tier.land hv _
      apply (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq
      unfold storm; ring

/-- All pairs through that endpoint (real roofs only, no assertion
this is a compatible localized alphabet). Also covers sum over all,
with coincident pair overcharge. -/
lemma pairHit {I : Type} [Fintype I] [DecidableEq I] {r : I → I → ℝ} {H : ℝ} (hr : ∀ i j,0≤r i j)
    (h : ∀ i, (∑ j,r i j) ≤ H) (hv : ∀ i, (∑ j,r j i) ≤ H) (s : Finset (I×I)) (i : I) :
    hits id s (fun u=>r u.1 u.2) i ≤ 2*H := by
  let f (j : I×I) := if j.1=i ∨ j.2=i then r j.1 j.2 else 0
  unfold hits meets; simp only [id_eq]; convert_to ∑ j∈s,f j≤2*H using 1
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t:=(Finset.univ : Finset (I × I))) (Finset.subset_univ _) (f:=f) (fun j _ _=> by
    unfold f; split; exact hr ..; rfl))
  let g (j : I×I) := (if j.1=i then r i j.2 else 0)+(if j.2=i then r j.1 i else 0)
  have he (j:I×I) : f j ≤ g j := by
    unfold f g; by_cases hA : j.1=i <;> by_cases hB : j.2=i <;> simp [hA,hB,hr]
  apply le_trans (Finset.sum_le_sum (fun j _=>he j)); unfold g; rw [Finset.sum_add_distrib]
  simp_rw [Fintype.sum_prod_type]; simp only [Finset.sum_ite_eq',Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_comm (s:=(Finset.univ:Finset I))]; simp [h,hv,two_mul,add_le_add]

lemma charges (a M B : ℝ) (hM : 0<M) (hB : 0≤B) {η : ℝ} (hη : 0<η) (hv : 0 < v) (ha : 0<a) :
    ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=Q →
      ∀ (A : Stores S) (F : Forest S.ratio), (∀ i, salt S A F x G a v M i ≤ 1) ∧
        ∀ Y j, hits id Y (fun i=>B*salt S A F x G a v M i) j ≤ η := by
  let y (x:ℝ) := colorInk G M*rate (-(a/4)) (radiusB x)
  have hy x : 0≤y x := mul_nonneg (zero_le_one.trans (colorInk_one G hM.le)) (rate_pos ..).le
  have ht : Tendsto y atTop (𝓝 0) := by
    have hi := Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp Work.E01.radiusB_tendsto)|>.const_mul_atTop_of_neg (neg_lt_zero.mpr (by linarith : 0<a/4)))
    simpa [y,rate,Function.comp_def] using hi.const_mul (colorInk G M)
  let u:=v/4
  have hu : 0<u := by unfold u; linarith
  filter_upwards [ht.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num)),
    (ht.const_mul (2*B*storm Q u)).eventually (ge_mem_nhds (by rw [mul_zero]; exact hη))] with x hz hx
  intro c f S hS A F
  let I := Active A x F
  let p := destination S A F (x:=x)
  have he (i j : I) : salt S A F x G a v M (i,j) = y x*rate (-u) (separation (p i) (p j)) := (mul_assoc ..).symm
  let X (i j:I):=B*salt S A F x G a v M (i,j)
  constructor
  · rintro ⟨i,j⟩; rw [he]; apply le_trans (mul_le_of_le_one_right (hy x) ?_) hz
    unfold rate; apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu.le) (Nat.cast_nonneg _)
  intro Y j
  have h (i) : (∑ j:I,X i j) ≤ (B*y x)*storm Q u := by
    have h := counted Q u S hS (p i) A F x hu
    unfold X; simp_rw [he,← mul_assoc B,← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h (mul_nonneg hB (hy x))
  have h' (i) : (∑ j:I,X j i) ≤ (B*y x)*storm Q u := by
    simp_rw [show ∀ i j, X j i=X i j from fun i j=> by unfold X; rw [he,he,separation_comm]]; exact h _
  have he := pairHit (fun i j=>mul_nonneg hB (salt_nn S A F x G a v M hM.le (i,j))) (r:=X) h h' Y j
  apply he.trans
  linarith only [hx]
end counts
end YM.AnalyticBridge.AnnulusRatioInsertions.Prism.Breeze
