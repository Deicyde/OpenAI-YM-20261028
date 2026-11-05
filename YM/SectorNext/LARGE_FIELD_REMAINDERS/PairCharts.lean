import YM.Bid.Station
import YM.Next.FLUCTUATIONS.Locality
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay
import YM.Work.B04


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Further estimate towards Gaussian normalization *without* spending the V cut

Ingredients for the pair gap. Work in the SAME local V gauges. Two different
U being compared: don't linearize one in the gauge of the other unless proving
legitimacy. Also permits two tags, using prediction linearization even for an
arbitrary tag near identity (shared loc transport) by `z_chart_cost`.
Everything in physical colors.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Center
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial  Next.Fluctuations Scales Metric   Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical  ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}

/-- Extension used for differencing. Don't pay norms of tree directions that
weren't certified. Tree links gauge-trivial still in common block gauge.
-/
lemma tree_chart_cost (G : Gauge) : ∃ C δ : ℝ, 0<C ∧ 0<δ ∧
    ∀ {c f : Side} (S : StepData c f) (F : Forest S.ratio) (q : Site c) (D : ℕ) (W : Config G f)
      (h : ℝ) (z : Site c → G.El), 0 ≤ h → h ≤ δ → SliceSet S F W →
      (∀ i : Bond f, separation q (S.ratio.parent i.1) ≤ D → G.chord (gauge (z∘S.ratio.parent) W i) ≤ h) →
        ∃ a : LogField G f, ‖a‖ ≤ C*h ∧ AgreeNear S.ratio.parent q D (gauge (z∘S.ratio.parent) W) (represent a) ∧
          ∀ i ∈ F.trunks, Exterior.collect G a i=0 := by
  obtain ⟨C,δ,hC,hr,H⟩ := extend_interior G
  refine ⟨C,δ,hC,hr,?_⟩
  intro c f S F q D W h z hh he hW hl
  obtain ⟨a,ha,hd⟩ := H _ _ _ _ _ hh he hl
  let e := Work.E03.poleEquiv f
  let b (i : Body 1 f) := if e.symm i ∈ F.trunks then 0 else a i
  have hval (i : Bond f) : Exterior.collect G b i = if i∈ F.trunks then 0 else Exterior.collect G a i := by
    change b (e i) = if _ then _ else a (e i); unfold b; rw [Equiv.symm_apply_apply]
  refine ⟨b, (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le hh)).mpr ?_,fun i hi => ?_,?_⟩
  · intro i; unfold b; split
    next hi => rw [norm_zero]; positivity
    next hi => exact (norm_le_pi_norm a i).trans ha
  · change _=G.lieExp (Exterior.collect G b i)*1
    rw [hval]; split
    next hv =>
      rw [G.mat_lieExp_zero,mul_one,Lattice.gauge,hW i hv,mul_one]
      simp only [Function.comp_apply,F.trunk_internal hv,mul_inv_cancel]
    next hv => exact hd i hi
  intro i hi; rw [hval,if_pos hi]

-- measured at chart radius (Taylor remainder, doesn't give Lipschitz inverses)
lemma distance_cost (G : Gauge) : ∃ C r : ℝ, 0<C ∧ 0<r ∧
    ∀ (q : ℝ) (u v : G.Color), q≤r → ‖u‖≤q → ‖v‖≤q →
    G.chord (G.lieExp u*(G.lieExp v)⁻¹) ≤ ‖u-v‖+C*q^2 := by
  let f := fun u : G.Color => G.mat (G.lieExp u)
  have he a : HasDerivAt (fun t : ℝ => f (t • a)) (G.colorMat a) 0 := by
    simp only [f,G.mat_lieExp,map_smul]; simpa using! hasDerivAt_exp_smul_const (G.colorMat a) (0:ℝ)
  obtain ⟨C,r,hC,hr,H⟩ := chart_quadratic_cost _ _ (G.exp_jet.contDiffAt.analyticAt) he
  let s := G.colorScale
  have hs : 0<s := G.colorScale_pos
  refine ⟨2*C/s, r, by positivity,hr,fun q u v hq hu hv => ?_⟩
  have hh a (h : ‖a‖ ≤ q) : ‖f a - (1+G.colorMat a)‖ ≤ C*q^2 := by
    have h1 := ((H a).2 (h.trans hq)).trans (show C*‖a‖^2≤C*q^2 by gcongr)
    simpa only [f,G.mat_lieExp_zero,G.mat_one] using! h1
  apply le_of_mul_le_mul_left (a:=s) _ hs
  change G.colorScale*_ ≤ _; rw [chord_gap]; change ‖f u-f v‖ ≤ _
  rw [show f u-f v=G.colorMat (u-v)+(f u-(1+G.colorMat u)-(f v-(1+G.colorMat v))) by rw [map_sub]; abel]
  apply (norm_add_le ..).trans
  apply (add_le_add_right (norm_sub_le ..) _).trans -- name switching
  rw [G.colorMat_norm]; change s*‖u-v‖+_ ≤ _
  field_simp; nlinarith [hh u hu,hh v hv]

lemma pred_turn (hS : S.patch.Branches S.kernel G) (U : Config G f) (V : Config G c) (z : Site c → G.El)
    (k : S.Choices) (i : Bond c) :
    Z S (S.prediction (gauge (z∘S.ratio.parent) U) k) (gauge z V) i = G.adjoint (z i.1) (Z S (S.prediction U k) V i) := by
  have hb : S.prediction (gauge (z ∘ S.ratio.parent) U) k = gauge z (S.prediction U k) := by
    funext e
    rw [StepData.prediction,S.updateGauged hS,(S.patch.bond_gauge (h:=hS) ..).2]
    simp only [Function.comp_apply,Ratio.embed_parent]; rfl
  rw [hb]; unfold Z Lattice.gauge
  rw [show z i.1 * V i * _ * (z i.1 * _ * _)⁻¹ = z i.1 * (V i * (S.prediction U k i)⁻¹) *
    (z i.1)⁻¹ by group,G.curvature_conjugate,map_smul]

lemma parts_sub (G : Gauge) {n : Side} {r : ℕ} (x y : Exterior.fieldDir G n r) (i : G.ColorIndex) :
    Exterior.parts G r (x-y) i = Exterior.parts G r x i - Exterior.parts G r y i := by ext; rfl

lemma bills_sub (G : Gauge) (x y : Bid.Dir G f) : Bid.bills S (x-y)=Bid.bills S x - Bid.bills S y := by
  ext i j; simp only [Bid.bills,parts_sub,Matrix.mulVec_sub,Pi.sub_apply]; rfl
lemma dColor_sub (G : Gauge) (x y : Bid.Dir G f) : dColor G f 1 (x-y)=dColor G f 1 x - dColor G f 1 y := by
  ext i j; simp only [dColor,parts_sub,Matrix.mulVec_sub,Pi.sub_apply]; rfl
lemma collect_sub (G : Gauge) (x y : Bid.Dir G f) : Exterior.collect G (x-y)=Exterior.collect G x - Exterior.collect G y := by ext; rfl

/-- Given chord patch prerequisites of `interior_cost`, use order one in log data to
price the bond and face differences in two fields. This does not spend the sieve.
Sup remainder allowance on every one address (including active boundary near a frozen
position). -/
lemma prediction_pair (S : StepData c f) (i : Bond c) (k l : S.Choices) (C h δ : ℝ) (hC : 0≤C)
    (hK : S.patch.Branches S.kernel G)
    (hq : ∀ k : S.Choices, ∀ u : PairLogs G f c, ‖u‖ ≤ δ →
      ‖zTest S k i u-zLin S u.1 u.2 i‖ ≤ C*‖u‖^2) (hu : h ≤ δ)
    (W W' : Config G f) (V : Config G c) (z : Site c → G.El)
    (a b : Bid.Dir G f) (v : Bid.Dir G c) (D : ℕ) (hR : predReach S.patch ≤ D)
    (ha : ‖a‖ ≤ h) (hb : ‖b‖ ≤ h) (hv : ‖v‖ ≤ h)
    (hva : AgreeNear S.ratio.parent i.1 D (gauge (z∘S.ratio.parent) W) (represent a))
    (hvb : AgreeNear S.ratio.parent i.1 D (gauge (z∘S.ratio.parent) W') (represent b))
    (hz : AgreeNear id i.1 D (gauge z V) (represent v)) :
    Real.sqrt S.kernel.penalty * ‖Bid.bills S (a-b) (pole i)‖ ≤
      ‖Z S (S.prediction W k) V i-Z S (S.prediction W' l) V i‖ + 2*(C*h^2) := by
  let A := zTest S k i (a,v)
  let B := zTest S l i (b,v)
  let Y := zLin S a v i
  let Z0 := zLin S b v i
  have he (w : Config G f) (a : Bid.Dir G f) (e : AgreeNear S.ratio.parent i.1 D (gauge (z∘S.ratio.parent) w) (represent a))
      (k : S.Choices) :
      zTest S k i (a,v) = G.adjoint (z i.1) (Z S (S.prediction w k) V i) := by
    rw [← pred_turn hK]
    unfold zTest Z
    rw [hz i (by change separation i.1 i.1 ≤ _; simp), prediction_near_eq hK _ _ k i (e.shrink (by rwa [separation_self,zero_add]))] -- Z uses (S.prediction ... k) value not at syntax i until unfold
  have hu' : ‖(a,v)‖ ≤ h := max_le ha hv
  have hv' : ‖(b,v)‖ ≤ h := max_le hb hv
  have h1 : ‖A-Y‖ ≤ C*h^2 := (hq k (a,v) (hu'.trans hu)).trans (by gcongr)
  have h2 : ‖B-Z0‖ ≤ C*h^2 := (hq l (b,v) (hv'.trans hu)).trans (by gcongr)
  have h3 : Y-Z0 = -Real.sqrt S.kernel.penalty • Bid.bills S (a-b) (pole i) := by
    unfold Y Z0 zLin
    rw [bills_sub,Pi.sub_apply]
    simp only [smul_sub,neg_smul]
    unfold Bid.bills; abel
  have ht : ‖A-B‖ = ‖Z S (S.prediction W k) V i-Z S (S.prediction W' l) V i‖ := by unfold A B; rw [he W a hva, he W' b hvb,← map_sub, G.norm_adjoint]
  rw [← Real.norm_of_nonneg (Real.sqrt_nonneg S.kernel.penalty), ← norm_smul]
  have hg : ‖Y-Z0‖ ≤ ‖A-B‖+2*(C*h^2) := by
    rw [show Y-Z0= (A-B) + (-(A-Y)+(B-Z0)) by abel]
    apply (norm_add_le ..).trans ((add_le_add_right ((norm_add_le ..).trans ?_) _))
    rw [norm_neg]; linarith
  rwa [h3,neg_smul,norm_neg,ht] at hg

lemma face_pair (S : StepData c f) (p : Cell f) (C h δ : ℝ) (hC : 0≤C)
    (hq : ∀ u : LogField G f, ‖u‖ ≤ δ →
      ‖G.curvature (faceValue (represent u) p)-Work.F03.faceCurl p u‖ ≤ C*‖u‖^2) (hu : h ≤ δ)
    (W W' : Config G f) (z : Site c → G.El) (o : Site c)
    (a b : Bid.Dir G f) (D : ℕ) (hR : separation o (S.ratio.parent p.1)+4 ≤ D)
    (ha : ‖a‖ ≤ h) (hb : ‖b‖ ≤ h)
    (hva : AgreeNear S.ratio.parent o D (gauge (z∘S.ratio.parent) W) (represent a))
    (hvb : AgreeNear S.ratio.parent o D (gauge (z∘S.ratio.parent) W') (represent b)) :
    ‖Work.F03.faceCurl p (a-b)‖ ≤ ‖G.curvature (faceValue W p)-G.curvature (faceValue W' p)‖+2*(C*h^2) := by
  let F := fun (u : LogField G f) => G.curvature (faceValue (represent u) p)
  let L := Work.F03.faceCurl (G:=G) p
  have he (w : Config G f) (u : Bid.Dir G f) (e : AgreeNear S.ratio.parent o D (gauge (z∘S.ratio.parent) w) (represent u)) :
      F u = G.adjoint (z (S.ratio.parent p.1)) (G.curvature (faceValue w p)) := by
    have hh : faceValue (gauge (z∘S.ratio.parent) w) p=faceValue (represent u) p := travel_near
      _ (Work.E03.parent_step S) _ _ p.1 (square p.2.val.1 p.2.val.2) 4 (by rfl) (e.shrink hR)
    unfold F; rw [← hh, face_gauge,G.curvature_conjugate,Function.comp_apply]
  have h1 : ‖F a-L a‖ ≤ C*h^2 := (hq a (ha.trans hu)).trans (by gcongr)
  have h2 : ‖F b-L b‖ ≤ C*h^2 := (hq b (hb.trans hu)).trans (by gcongr)
  have h3 : L a-L b = L (a-b) := by unfold L Work.F03.faceCurl; rw [dColor_sub]; rfl
  rw [← G.norm_adjoint (z (S.ratio.parent p.1)) ( _ - _), map_sub, ← he W a hva, ← he W' b hvb]; change ‖L (a-b)‖≤_; rw [← h3]
  rw [show L a-L b= (F a-F b) + (-(F a-L a)+(F b-L b)) by abel]
  apply (norm_add_le ..).trans ((add_le_add_right ((norm_add_le ..).trans ?_) _))
  rw [norm_neg]; linarith

end YM.SectorNext.Remainder.Center
