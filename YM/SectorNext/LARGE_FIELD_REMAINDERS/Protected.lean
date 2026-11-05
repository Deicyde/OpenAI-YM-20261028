import YM.SectorNext.LARGE_FIELD_REMAINDERS.CorePacket


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Integrability and quantitative costs of protected real packet multipliers

Even if hard U predicates not differentiated anywhere, need legit bounds on the
*integral*. k/V held fixed. Work with patch parameters mapped measurably into the
genuine Wilson sectors of these callers. Typical upstream obligation: supply this
map & the still-retained Borel profiles forcing the recorded Wide/Owns etc, and
establish their correct ingredients; e.g. at fixed frozen Haar and integrated
positions. All fderivs in affine terms then legal; only need Borel on the protected
reads. Don't assert smoothness across switches in any row. Products not assumed
integrable.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric Oriented Presented Exterior Bloch Work.F03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff ENNReal

variable {G : Gauge} {c f n : Side} {S : StepData c f} {X : Type*} [MeasurableSpace X]

set_option maxHeartbeats 580000 in
private lemma window_meas (P : Teller G) (T : Tube G S) (x : ℝ) (W : Window S) (k : S.Choices) (V : Config G c)
    (ht : P.Funds S T) : Measurable (fun U => W.work T x U k V) := by
  obtain ⟨a,b,ha,hb⟩ := ht.feeds
  rw [← ht.high] at ha
  let t := fiery G x S.patch.L; let R := till x
  let H := S.prediction (G:=G)
  have hF (i : Cell f) : Measurable (fun U : Config G f => T.workF R U V t (temp x) i) := by
    unfold workF
    exact (env_crown ha _ _ _ _|>.meas).add (Finset.measurable_fun_sum _ fun j _ =>
      (continuous_const.sub (continuous_const.inner (plotted_cont ha ..))).measurable)
  have hI (i : Bond c) : Measurable (fun U : Config G f => T.workI R (H U k) V (temp x) i) :=
    (show Continuous (fun Q : Config G c => T.workI R Q V (temp x) i) by unfold workI monetary wire Z; fun_prop).measurable.comp
      (S.prediction_meas (funds_branch ht) k)
  have hL (i : Cell c) : Measurable (fun U : Config G f => T.workL R U (H U k) V (temp x) i) := by
    let F (u : Config G f × Config G c) := T.workL R u.1 u.2 V (temp x) i
    have he : Continuous F := by
      unfold F workL unzip Z
      have h (a : Twin f) := plotted_cont ha R 1 a
      unfold Xf; fun_prop
    have ha : Measurable (fun u : Config G f => (u,S.prediction u k)) := measurable_id.prodMk (S.prediction_meas (funds_branch ht) k)
    exact he.measurable.comp (f:=fun u : Config G f => (u,S.prediction u k)) ha
  unfold Window.work onWindow
  refine (((Finset.measurable_fun_sum _ (fun i _ => hF i)).add (Finset.measurable_fun_sum _ (fun i _ => hI i))).add
    (Finset.measurable_fun_sum _ (fun i _ => measurable_const.add ((hL i).add measurable_const)))).add measurable_const

private lemma safe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (K : X → ℝ → E) (he : ∀ t : ℝ, Measurable (fun x => K x t)) (h : Set X) (hh : MeasurableSet h) (hf : ∀ x∈h, DifferentiableAt ℝ (K x) 0) :
    Measurable (h.indicator (fun x => deriv (K x) 0)) := by
  let v n := ((n:ℕ)+1:ℝ)⁻¹
  have hv : Tendsto v atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop (R:=ℝ))),?_⟩
    exact Eventually.of_forall fun i => Set.mem_compl_singleton_iff.mpr (by unfold v; positivity)
  let F n := h.indicator fun a => slope (K a) 0 (v n)
  have hF n : Measurable (F n) := ((measurable_const (a:=((v n)-0)⁻¹)).smul ((he (v n)).sub (he 0))).indicator hh
  apply measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.mpr _)
  intro a; by_cases h : a∈h
  · simpa [F,h,Function.comp_def] using ((hf _ h).hasDerivAt.tendsto_slope.comp hv)
  simp [F,h]

private lemma step_ok {Y : Type*} [MeasurableSpace Y] (n : Side) (W : Config G n) (a : Y → Directions G n) (h : Measurable a) (r : ℝ) :
    Measurable (fun y => increment W (r • a y)) := by
  unfold increment
  have hl (e) : Measurable fun y => a y e := (measurable_pi_apply e).comp h
  apply measurable_pi_lambda
  intro i; exact (G.lieExp_cont.measurable.comp (measurable_const.smul (hl i))).mul measurable_const

set_option maxHeartbeats 580000 in
/-- Measurable on the ambient integrate-space once protected. At zero profile
weight don't try to read a smooth tangent. -/
lemma check (P : Teller G) (T : Tube G S) (hT : P.Funds S T) (x β : ℝ) (O : Stores S) (V : Config G c) (k : S.Choices)
    (U : X → Config G f) (a : X → Signed → Directions G f) (χ : X → ℝ) (Q J : Signed → Window S)
    (h : Measurable U) (ha : Measurable a) (hc : Measurable χ)
    (he : ∀ y, χ y ≠ 0 → ∀ s, (J s).written T x (choice s k) (pull s 0 V) (a y s)) :
    Measurable (fun y => χ y * vital β x (U y) V O Q J T k (a y)) := by
  let D : Set X := {i | χ i≠0}
  have hD : MeasurableSet D := (hc (measurableSet_singleton 0)).compl
  have hb := funds_branch hT
  -- on every oriented window extend needed numerical derivatives from D,
  -- and the rest of the work reads are measurable already
  have hx (s : Signed) : ∃ w : X → ℝ, Measurable w ∧
      ∀ i ∈ D,w i=credits (U i) V O Q J T x k (a i) s := by
    let p := fun i => a i s
    let V' := pull s 0 V; let W := replica S.ratio V'; let k' := choice s k
    let U' := fun i => pull s 0 (U i)
    let O' := turnStore s O
    let L i := O'.assessed T x (U' i) (S.prediction (U' i) k') V'+(Q s).work T x (U' i) k' V'
    have hu : Measurable U' := pulling_meas s h
    have hL : Measurable L := (env_assessed (V:=fun _ => V') hT x k' hu measurable_const O').meas.add ((window_meas P T x (Q s) k' V' hT).comp hu)
    have hp : Measurable p := (measurable_pi_apply s).comp ha
    let N (i : Cell f) := D.indicator (fun j => faceVar W (p j) i)
    let M (i : Bond c) := D.indicator (fun j => qVar S W i k' (p j))
    have hf (i : Cell f) (h : ∀ j∈D, DifferentiableAt ℝ (fun t : ℝ => G.curvature (faceValue (increment W (t • p j)) i)) 0) : Measurable (N i) := by
      apply safe (fun j t => G.curvature (faceValue (increment W (t • p j)) i)) _ _ hD h
      intro t; refine (show Continuous (fun u : Config G f => G.curvature (faceValue u i)) by unfold faceValue; fun_prop).measurable.comp
        (step_ok f W p hp t)
    have hm (i : Bond c) (h : ∀ j∈D, DifferentiableAt ℝ (fun t : ℝ => G.curvature (actuate S W i k' (p j) t*(actuate S W i k' (p j) 0)⁻¹)) 0) : Measurable (M i) := by
      apply safe (fun j t => G.curvature (actuate S W i k' (p j) t*(actuate S W i k' (p j) 0)⁻¹)) _ _ hD h
      have hn t : Measurable (fun j : X => actuate S W i k' (p j) t) := (measurable_pi_apply i).comp
        ((S.prediction_meas hb k').comp (step_ok f W p hp t))
      intro t; exact G.continuous_curvature.measurable.comp ((hn t).mul (hn 0).inv)
    let v (i : Cell f) (m : ℕ) := (T.up.row i.2 m).2
    let n i j := G.curvature (faceValue W i) + N i j
    let mass (i : Cell f) m j := if (v i m).length ≤ till x then
        (T.up.row i.2 m).1 • G.adjoint (travel W i.1 (v i m).walk) (n (Work.F03.slotFace (v i m) i.1) j) else 0
    let e (i : Cell f) j := ‖Real.sqrt T.high.direct • (n i j) - T.Mv (till x) (temp x) V' (i,false)‖^2/2 +
      ‖(∑' t : ℕ,mass i t j)-T.Mv (till x) (temp x) V' (i,true)‖^2/2
    let g (i : Bond c) j := ‖(Z S (S.prediction W k') V' i - Real.sqrt S.kernel.penalty • M i j) - T.Mw (till x) (temp x) V' i‖^2/2
    let f j := (∑ i∈ (J s).face,e i j)+(∑ i∈(J s).noise,g i j)
    refine ⟨fun j => L j-f j,hL.sub ((Finset.measurable_fun_sum _ (fun i hi => ?_)).add (Finset.measurable_fun_sum _ (fun i hi => ?_))),fun i hi => ?_⟩
    · have hb : Measurable (n i) := measurable_const.add (hf _ (fun j hj => ((he _ hj s).1 _ hi).2.1))
      refine Measurable.add ?_ ?_
      · have hsc : Measurable (fun j => Real.sqrt T.high.direct • n i j) := (measurable_const (a:=Real.sqrt T.high.direct)).smul hb
        exact ((hsc.sub measurable_const).norm.pow_const 2).div_const 2
      suffices ht : Measurable (fun j => ∑' t : ℕ,mass i t j) from ((ht.sub measurable_const).norm.pow_const 2).div_const 2
      apply Measurable.tsum; intro t; unfold mass; split
      next h => exact (measurable_const (a:=(T.up.row i.2 t).1)).smul ((G.adjoint (travel W i.1 (v i t).walk)).continuous_of_finiteDimensional.measurable.comp
        ((measurable_const (a:=G.curvature (faceValue W _))).add (hf _ (fun j hj => ((he _ hj s).1 _ hi).2.2 _ h))))
      next _ => exact measurable_const
    · have h : Measurable (fun i₀ => Real.sqrt S.kernel.penalty • M i i₀) := (measurable_const (a:=Real.sqrt S.kernel.penalty)).smul
        (hm i (fun j hj => ((he j hj s).2 i hi).1))
      exact (((measurable_const.sub h).sub measurable_const).norm.pow_const 2).div_const 2
    · have hn j : N j i = faceVar W (p i) j := Set.indicator_of_mem hi _
      have hm j : M j i = qVar S W j k' (p i) := Set.indicator_of_mem hi _
      unfold L f e g mass v n credits boost Window.extract squareP squareQ affF0 affF1 firstCut perCharge firstSlot firstFace
      simp only [hn,hm]; unfold O' k' U' W p V'; change _ + _ - (_+_)=_+(_-(_+_)); abel
  choose q hq hf using hx
  let w (i : X) := Real.exp (-β*averaged fun s => q s i)
  have hw : Measurable w := (measurable_const.mul (measurable_const.mul (Finset.measurable_fun_sum _ (fun i _ => hq i)))).exp
  refine (show (fun y => χ y * vital β x (U y) V O Q J T k (a y)) = _ from ?_) ▸ hc.mul hw
  funext i; by_cases he : i∈D
  · change _ = χ i*w i; unfold w vital; simp_rw [fun j => hf j i he]
  have h : χ i=0 := not_not.mp he; change _ = χ i*w i; simp only [h,zero_mul]
end YM.SectorNext.Remainder.Affine

noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric Oriented Presented Exterior Bloch Work.F03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff ENNReal

variable {G : Gauge} {c f n : Side} {S : StepData c f} {X : Type*} [MeasurableSpace X]
  (P : Teller G) (T : Tube G S) (L : Side) (x W κ K H β B : ℝ) (n' D' : ℕ)
  (hT : P.Funds S T) (hL : S.patch.L=L) (hs : 100*(1+radiusB x)≤c.val)
  (hp : PointCharge T x W κ) (hc : Ledger P L W κ K H n' D' x)
  (hβ : β∈Set.Icc (y G L x/2) (2*y G L x)) (hB : 0 ≤ B)
  (Q J : Signed → Window S) (F : Forest S.ratio) (O A : Stores S) (V : Config G c)
  (k : S.Choices) (a : X → Signed → Directions G f)
  (U : X → Config G f) (hU : Measurable U) (ha : Measurable a)
  (χ : X → ℝ)

def valuation (O : Stores S) (l : ℝ) (n : ℕ) (x : ℝ) (G : Gauge) := coin G S.patch.L l n x*O.shares

def remaining (O : Stores S) (G : Gauge) (x κ : ℝ) := Real.exp (-κ/4 * p G S.patch.L x^2 * O.shares)

def Comp (i : X) := χ i * vital β x (U i) V O Q J T k (a i)

def protection (O A : Stores S) (F : Forest S.ratio) (D' : ℕ) (K W x : ℝ)
    (i : X) : Prop :=
    χ i ≠0 → SliceSet S F (U i) ∧ ∀ s, Ensures (U i) V O Q J x k (a i) W K D' F A s

include hc hU ha hp hB hβ hL hs hT

/-- Genuine protected procurement.

`χ` models product of real default/nondefault,
K, q, analytic branch, etc compulsory factors; need the Borel and named affordability
receipts and exact local prerequisites on their support.

Even if measure is only
*conditional* probability (e.g. on frozen arguments fixed), packet can be charged
in that integral.

Can't put other
formulas there; for any others provide real estimates separately.

Allow ρ price log
reserve besides the multiplier's own χ cost (include prices through supports or
counts if post-L & THEN setting delay anew); handy in summed integrals. -/
lemma protected_purchase (ρ : ℝ) (ht : Measurable χ)
    (hd : ∀ i, protection Q J V k a U χ O A F D' K W x i)
    (he : ∀ i, Real.exp ρ * ‖χ i‖ ≤ B * Real.exp (valuation O H n' x G)) :
    Measurable (Comp T x β Q J O V k a U χ) ∧
    (∀ i, Real.exp ρ * ‖Comp T x β Q J O V k a U χ i‖ ≤ B * remaining O G x κ) ∧
    ∀ μ : MeasureTheory.Measure X, ∀ (_ : IsProbabilityMeasure μ),
      Integrable (Comp T x β Q J O V k a U χ) μ ∧
      Real.exp ρ * ∫ i : X, ‖Comp T x β Q J O V k a U χ i‖ ∂μ ≤ B*remaining O G x κ := by
  let N := Comp T x β Q J O V k a U χ
  have h (i : X) (P' : χ i ≠ 0) := used (U i) V O Q J k (a i) F A hL hs hT β K H W κ D' n' hp hc hβ ((hd i P').1) ((hd i P').2)
  have hm : Measurable N := check P T hT x β O V k U a χ Q J hU ha ht (fun i hi => (h i hi).1)
  let Uc := valuation O H n' x G
  let c0 := B*remaining O G x κ
  have hh i : Real.exp ρ * ‖N i‖ ≤ c0 := by
    by_cases hz : χ i=0
    · unfold N Comp; rw [hz,zero_mul,norm_zero,mul_zero]; exact mul_nonneg hB (Real.exp_pos _).le
    unfold N Comp; rw [norm_mul, Real.norm_of_nonneg (show 0≤vital β x (U i) V O Q J T k (a i) from (Real.exp_pos _).le), ← mul_assoc]; apply (mul_le_mul (he i) (h i hz).2
      (Real.exp_pos _).le (mul_nonneg hB (Real.exp_pos _).le)).trans_eq
    unfold valuation c0 remaining; rw [hL,Real.exp_sub]
    field_simp
  refine ⟨hm,hh,?_⟩; intro μ Hμ
  have hd : Envelope N := ⟨hm,c0/Real.exp ρ,fun i => (le_div_iff₀ (Real.exp_pos _)).mpr (by rw [mul_comm]; exact hh i)⟩
  have hi := hd.integrable μ
  refine ⟨hi,?_⟩
  rw [← integral_const_mul]; exact (integral_mono (hi.norm.const_mul _) (integrable_const c0) hh).trans_eq (by simp; rfl)

end YM.SectorNext.Remainder.Affine
