import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.TellerFold
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Scales
import YM.UVNext.PRICED_KERNELS.Read



/-!
# Buying the CURL of the uncut deterministic mean on the same data

and argument akin to the psi/k comparison in 
(but NOT switching radii or g or cutting psi). Pt.C also buys L^-2 in
Fund's actual towers. We require extra true strip prices of the two retained
Beds. Can narrow widths to use one common positive s ≤ Pt.η. Not just an
estimate on abstract PSD beds with no width. No volume factors. Off the
clear region, k(V) can be order 1: don't apply k(V) ≤ t' there!

The Psi we price is EXACTLY for use with fConditional of the *same* H,B,
not swapping in, say, one calculated with H.inverse. Thus can combine the
two parts even though treeInverse still in tree coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Pressure.Stores Gaussian Tree Bid FreeResolvent
open Extra.Iteration Extra.Iteration.Scales UVNext.PricedKernels
open YM.AnalyticBridge.LocalGaussianLaws Current Lift Remote 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}

/-- Given these strip prices before choosing block widths. -/
def psiCost (s E A B : ℝ) : ℝ := ((Fintype.card (TypeFace 2) : ℝ)*A) * stackFee s E (TypeFace 2) *
  ((Fintype.card (TypeFace 2) : ℝ)*B)
lemma psiCost_nonneg {s E A B : ℝ} (he : 0≤E) (ha : 0≤A) (hb : 0≤B) : 0≤psiCost s E A B := by
  unfold psiCost
  have ht := stackFee_nonneg s (TypeFace 2) he
  positivity

lemma psi_rows (Pt : Teller G) {A B C : ℝ} (hs : 0 ≤ C) (hb : 0 ≤ B) (he : 0 ≤ Pt.C)
    (hr : C ≤ Pt.η) (T : Tube G S) (H L : Bed) (hf : H.covered C A) (hh : L.covered C B) (ht : Pt.Funds S T) :
    let m : ℝ := S.patch.L.val
    Annuity (site f _) (UVNext.PricedKernels.parent S.ratio _) (psi S H L T.R) (C/m) (psiCost C Pt.C A B/m^2) := by
  intro m
  have hm : 1 ≤ m := Nat.one_le_cast.mpr S.patch.L.property
  have hx : 0 < m := zero_lt_one.trans_le hm
  have hp := div_nonneg hs hx.le
  have hv : T.R.T.strip C (Pt.C/m^2) :=
    Work.F08.strip_mono (show T.R.T.strip Pt.η (Pt.C/m^2) from (ht.crosses.2.2.2 [] (Nat.zero_le _)).2) hr le_rfl
  have hi := Annuity.paid_cross (g:=S.ratio) hv hs
  have h1 := (Annuity.paid_site hf.2.2.2.2 hs f).cut (div_le_self hs hm) le_rfl
  have h2 := (Annuity.paid_parent S.ratio hh.1 hs)
  apply ((h1.times hi hp (by positivity)).times h2 hp (by positivity)).cut le_rfl
  exact le_of_eq (by unfold psiCost stackFee; ring)

abbrev Curvature (G : Gauge) (n : Side) := Exterior.fieldDir G n 2
def look (U : Config G n) : Curvature G n := fun i =>
    G.curvature (faceValue U (i.1,plaqEquiv.symm i.2))
lemma looking (U : Config G n) (p : Cell n) : look U (p.1,plaquette p.2) = G.curvature (faceValue U p) := by
  unfold look; rw [show plaqEquiv.symm (plaquette p.2)=p.2 from plaqEquiv.symm_apply_apply _]

/-- Apply FULL Psi to colors. -/
def flow (S : StepData c f) (H L : Bed) (T : Tube G S) (V : Curvature G c) : Curvature G f := fun i =>
  WithLp.toLp 2 fun k => (psi S H L T.R *ᵥ parts G 2 V k) i

lemma flow_spins (F : Forest S.ratio) (H B : Bed) (T : Tube G S) {a M : ℝ} (hH : Floor H T.high f a M)
    (hT : Towers.Diagonal S H B T.R) (v : Dir G c) :
    dColor G f 1 (low T F v) = flow S H B T (dColor G c 1 v) := by
  funext i; ext k
  change (d 1 f *ᵥ parts G 1 (low T F v) k) i = (psi S H B T.R *ᵥ (d 1 c *ᵥ parts G 1 v k)) i
  rw [show parts G 1 (low T F v) k = neuron S F T.R *ᵥ parts G 1 v k from
    Work.F04.parts_stretch F (installed S.ratio T.R.A0) v k,mulVec_mulVec,mulVec_mulVec,spins S F H B T.R hT hH]
lemma flow_sub (H L : Bed) (T : Tube G S) (W V : Curvature G c) :
    flow S H L T W-flow S H L T V=flow S H L T (W-V) := by
  funext i; ext k
  change (psi S H L T.R *ᵥ parts G 2 W k) i-(psi S H L T.R *ᵥ parts G 2 V k) i=
    (psi S H L T.R *ᵥ (parts G 2 W k-parts G 2 V k)) i
  rw [Matrix.mulVec_sub]; rfl

lemma flow_norm (H L : Bed) (T : Tube G S) {s R b : ℝ} (V : Curvature G c)
    (h : Annuity (site f _) (UVNext.PricedKernels.parent S.ratio _) (psi S H L T.R) s R)
    (hb : 0≤b) (hR : 0≤R) (i : Body 2 f)
    (he : ∀ j, ‖V j‖ ≤ b*gained s i.1 (S.ratio.embed j.1)) :
    ‖flow S H L T V i‖ ≤ (Fintype.card G.ColorIndex:ℝ)*(R*b) :=
  color_count (mul_nonneg hR hb) _ (fun k => gather h i hb (fun j =>
    (color_component (V j) k).trans (he j)))


def Spacing (G : Gauge) (L : Side) (s E A B : ℝ) : Prop :=
    let m : ℝ := L.val
    (Fintype.card G.ColorIndex:ℝ) * (psiCost s E A B/m^2) * 2 ≤ 1/4096



/-- gain if the INPUT stencil of Psi is far. separation in its rate is
*not* separation o j. Pay for their discrepancy. -/
lemma far_gain {s : ℝ} (hp : 0<s) (p : Site f) (j o : Site c) {B : ℕ}
    (hB : 100 ≤ B) (h : separation o (S.ratio.parent p) ≤ B/4) (hh : B/2 < separation o j) :
    let L : ℝ := S.patch.L.val
    Real.exp ((s/8)*(B:ℝ)) ≤ gained (s/L) p (S.ratio.embed j) := by
  intro L
  have hL : 0 < L := by unfold L; exact Nat.cast_pos.mpr S.patch.L.property
  let r := S.ratio.parent p
  have he : separation o j ≤ separation o r + separation r j := separation_triangle _ _ _
  change separation o r ≤ _ at h
  have hi : (B:ℝ) ≤ 4 * (separation r j:ℝ) := by exact_mod_cast (show B ≤ 4*separation r j by omega)
  have H : L*(separation r j:ℝ) ≤ (separation (S.ratio.embed r) (S.ratio.embed j):ℝ) := by
    unfold L
    exact_mod_cast Lattice.Corona.below S.ratio r j
  have hx := Lattice.Corona.near S.ratio p
  have hX : 2*(separation p (S.ratio.embed r):ℝ) ≤ L := by unfold L; exact_mod_cast hx
  have hw : (separation (S.ratio.embed r) (S.ratio.embed j):ℝ) ≤ (separation p (S.ratio.embed r):ℝ) +
      (separation p (S.ratio.embed j):ℝ) := by
    rw [separation_comm p]; exact_mod_cast (separation_triangle (S.ratio.embed r) p (S.ratio.embed j))
  have hu : 100 ≤ (B:ℝ) := by exact_mod_cast hB
  have hg : (B:ℝ)/8*L ≤ (separation p (S.ratio.embed j):ℝ) := by
    nlinarith only [H,hX,hw,mul_le_mul_of_nonneg_left hi hL.le,mul_le_mul_of_nonneg_left hu hL.le,hL]
  apply Real.exp_le_exp.mpr
  exact Eq.trans_le (show s/8*(B:ℝ)= (s/L)*((B:ℝ)/8*L) by field_simp)
    (mul_le_mul_of_nonneg_left hg (div_nonneg hp.le hL.le))

private lemma expSpends {C s : ℝ} (hs : 0<s) (hC : 0 ≤ C) : ∀ᶠ x : ℝ in atTop,
    C ≤ temp x * Real.exp ((s/8)*(radiusB x:ℝ)) ∧ C ≤ linkRoom x ^ 2 * Real.exp ((s/8)*(radiusB x:ℝ)) := by
  filter_upwards [eventually_ge_atTop 1, first (s/8) 1 (by positivity), const_allow hC (show (-1:ℝ)< -(3/4) by norm_num)] with x hx he hh
  have hp := zero_lt_one.trans_le hx
  let y := s/8 * radiusB x
  have hv : C ≤ linkRoom x^2 * Real.exp y := by
    apply (div_le_iff₀ (Real.exp_pos _)).mp
    rw [div_eq_mul_inv,← Real.exp_neg,linkRoom_sq hp]
    exact (mul_le_mul_of_nonneg_left (show Real.exp (-y) ≤ x^(-1:ℝ) by unfold y; rwa [← neg_mul]) hC).trans hh
  refine ⟨hv.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le),hv⟩
  rw [linkRoom_sq hp]
  apply (Real.rpow_le_rpow_of_exponent_le hx (show (-(3/4):ℝ) ≤ -(1/2:ℝ) by norm_num)).trans
  rw [Real.rpow_neg hp.le,← Real.sqrt_eq_rpow]
  change _ ≤ _ * meter x
  exact le_mul_of_one_le_right (by positivity) (meter_ge _)

lemma near_face (V U : Config G c) (p : Cell c) {o : Site c} {B : ℕ}
    (h : separation o p.1 + 1 ≤ B) (he : AgreeNear id o B V U) : faceValue V p = faceValue U p := by
  have hh (i : Axis) : separation o (p.1+step i) ≤ B :=
    (separation_triangle ..).trans ((Nat.add_le_add_left (Work.E01.sep_step_le p.1 i) (separation o p.1)).trans h)
  change faceValue V (p.1,p.2) = faceValue U (p.1,p.2)
  rw [corners, corners, he (p.1,p.2.val.1) (show separation o p.1 ≤ B by omega),
    he (p.1+step p.2.val.1,p.2.val.2) (hh _), he (p.1+step p.2.val.2,p.2.val.1) (hh _),
    he (p.1,p.2.val.2) (show separation o p.1 ≤ B by omega)]

lemma k_size {x : ℝ} {o : Site c} (A : Stores S) (U : Config G c) (p : Cell c)
    (hi : separation o p.1 ≤ radiusB x) (hh : Clears A x o (radiusB x)) (hz : A.flags=RG.flags (temp x) U) :
    ‖look U (p.1,plaquette p.2)‖ ≤ temp x := by
  rw [looking]
  refine (G.curvature_norm _).trans ?_
  by_contra! ht
  apply hh; apply halo_spec.mpr
  have he : p.1∈A.flags := by
    rw [hz]
    exact (flags_spec ..).2 ⟨p,Work.E01.base_touched p,ht⟩
  exact ⟨p.1,mem_union_right _ he,(separation_comm ..).trans_le (by omega)⟩

lemma paying_inputs (G : Gauge) {s : ℝ} (hs : 0<s) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f) (o : Site c) (A : Stores S),
    Clears A x o (radiusB x) → ∀ U : Config G c, A.flags=RG.flags (temp x) U →
    ∀ v : Dir G c, AgreeNear id o (radiusB x) U (represent v) → ‖v‖ ≤ linkRoom x →
    ∀ p : Body 2 f, separation o (S.ratio.parent p.1) ≤ radiusB x / 4 →
    ∀ j : Body 2 c,
      let F := gained (s/(S.patch.L.val:ℝ)) p.1 (S.ratio.embed j.1)
      ‖look U j‖ ≤ temp x * F ∧ ‖(dColor G c 1 v - look U) j‖ ≤ D * linkRoom x ^ 2 * F := by
  obtain ⟨D,r,hD,hr,h⟩ := face_chart_cost G
  let C := max D 1
  have hC : 1 ≤ C := le_max_right ..
  have h2 : D≤C := le_max_left ..
  refine ⟨C,hD.le.trans h2,?_⟩
  filter_upwards [expSpends (C:=D+2) hs (by linarith),Work.E01.radiusB_tendsto.eventually_ge_atTop 100,
    linkRoom_tends.eventually (ge_mem_nhds (show 0 < min 1 r from lt_min zero_lt_one hr)),
    eventually_gt_atTop (0:ℝ)] with x hx hv hQ hX
  intro c f S o A hh U hA v hu hb p hP j F
  obtain ⟨y,t⟩ := j
  obtain ⟨b,rfl⟩ := plaqEquiv.surjective t
  have hf : 1 ≤ F := Real.one_le_exp (by have hi : 0 < (S.patch.L.val:ℝ) := Nat.cast_pos.mpr S.patch.L.property; positivity)
  let q : Cell c := (y,b)
  by_cases he : separation o y ≤ radiusB x / 2
  · refine ⟨(k_size A U q (he.trans (by omega)) hh hA).trans (le_mul_of_one_le_right ((Work.E09.temp_pos hX).le) hf),?_⟩
    change ‖(Work.F03.faceCurl q v - look U (q.1,plaquette q.2))‖ ≤ _
    rw [looking,near_face U (represent v) q (by change separation o y+_≤_; omega) hu,norm_sub_rev]
    apply (((h v q).2 (hb.trans (hQ.trans (min_le_right ..))))).trans
    apply le_trans _ (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hC) (sq_nonneg _)) hf)
    exact mul_le_mul h2 (pow_le_pow_left₀ (norm_nonneg _) hb _) (sq_nonneg _) (zero_le_one.trans hC)
  have hS := far_gain p.1 y o hv hP (lt_of_not_ge he) (hp:=hs)
  have hr : ‖look U (q.1,plaquette q.2)‖ ≤ 2 := by rw [looking]; exact (G.curvature_norm _).trans (G.chord_le_two _)
  refine ⟨hr.trans ((show 2 ≤ D+2 by linarith).trans (hx.1.trans
    (mul_le_mul_of_nonneg_left hS ((Work.E09.temp_pos hX).le)))),?_⟩
  change ‖Work.F03.faceCurl q v - look U (q.1,plaquette q.2)‖ ≤ _
  apply (norm_sub_le ..).trans
  have hd : ‖Work.F03.faceCurl q v‖ ≤ D := ((h v q).1).trans
    (mul_le_of_le_one_right hD.le (hb.trans (hQ.trans (min_le_left ..))))
  refine (add_le_add hd hr).trans (hx.2.trans (mul_le_mul ?_ hS (Real.exp_pos _).le ?_))
  · exact le_mul_of_one_le_left (sq_nonneg _) hC
  exact mul_nonneg (zero_le_one.trans hC) (sq_nonneg _)

theorem curl_budget (G : Gauge) (P : Patch) (Pt : Teller G) {s a b : ℝ} (hs : 0 < s)
    (hr : s ≤ Pt.η) (hA : 0 ≤ a) (hB : 0 ≤ b) (he : 0 ≤ Pt.C) (hS : Spacing G P.L s Pt.C a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T → ∀ H L : Bed,
    ∀ u V : ℝ, Floor H T.high f u V → Towers.Diagonal S H L T.R → H.covered s a → L.covered s b →
    ∀ o : Site c, ∀ (A : Stores S), Clears A x o (radiusB x) → ∀ U : Config G c, A.flags=RG.flags (temp x) U →
    ∀ v : Dir G c, AgreeNear id o (radiusB x) U (represent v) → ‖v‖ ≤ linkRoom x →
    ∀ (F : Forest S.ratio) (i : Body 2 f), separation o (S.ratio.parent i.1) ≤ radiusB x/4 →
    let t := fiery G x P.L; let h := linkRoom x
    let k := flow S H L T (look U) i; let z := dColor G f 1 (low T F v) i
    ‖z-k‖ ≤ C*h^2 ∧ ‖k‖ ≤ t/4096 ∧ ‖z‖ ≤ t/2048 := by
  let K := (Fintype.card G.ColorIndex:ℝ); let R := psiCost s Pt.C a b/(P.L.val:ℝ)^2
  have hk : 0≤K := Nat.cast_nonneg _
  have hR : 0 ≤ R := div_nonneg (psiCost_nonneg he hA hB) (sq_nonneg _)
  obtain ⟨D,hD,h⟩ := paying_inputs G hs
  let C := K*R*D; have hC : 0 ≤ C := by unfold C; positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [h, across G P.L, threshold_large G P.L (4096*C) (by positivity)] with x hx hT' hX
  obtain ⟨-,ht',ht,hh,-⟩ := hT'
  intro c f S T hP H0 H L u V hH hT ha hb o A ho U hU v hg hv F i hi t z k y
  let Y := s/(S.patch.L.val:ℝ)
  have hy : Annuity (site f _) (UVNext.PricedKernels.parent S.ratio _) (psi S H L T.R) Y R := by
    have hf := psi_rows Pt hs.le hB he hr T H L ha hb H0
    change Annuity _ _ _ _ (psiCost s Pt.C a b/(S.patch.L.val:ℝ)^2) at hf
    exact (Annuity.cut hf le_rfl (le_of_eq (by rw [hP])))
  have h₁ := hx S o A ho U hU v hg hv i hi
  have h₂ : ‖y-k‖ ≤ C*z^2 := by
    have he : y-k=flow S H L T (dColor G c 1 v-look U) i := by
      unfold y k; rw [flow_spins F H L T hH hT]; exact congr_fun (flow_sub ..) i
    rw [he]
    exact (flow_norm H L T (dColor G c 1 v-look U) hy (mul_nonneg hD (sq_nonneg _)) hR i (fun j => (h₁ j).2)).trans_eq (by
      change K*(R*(D*z^2))=C*z^2; unfold C; ring)
  have hw : ‖k‖ ≤ t/4096 := by
    apply (flow_norm H L T (look U) hy ht'.le hR i (fun j => (h₁ j).1)).trans
    calc
      K*(R*temp x) ≤ K*(R*(2*t)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hR) hk
      _ = K*R*2*t := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right (show K*R*2 ≤ 1/4096 from hS) ht.le).trans_eq (by ring)
  refine ⟨h₂,hw,(norm_le_norm_sub_add y k).trans ?_⟩
  change _ ≤ t/2048
  have hp : 4096*C*z^2 ≤ t := hX
  linarith only [hp,h₂,hw]
end YM.PhysicalNext.PhysicalGuard7f546.Curved
