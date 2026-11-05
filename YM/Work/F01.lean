import YM.Analysis.Polydisc
import YM.Bid.Station
import YM.PREC.Derivative

/-!
# Fixed-L gap in real counting coordinates (F01)

Use the shell comparison E02 on the actual slice, approaching 1 along real
exponential lines there. This sees both the coboundary and the derivative of
the actual predictor. Count macro costs only after fixing L. All `‖ ‖` on
individual colors are physical; avoid Pi-norm estimates with period costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F01
open Filter Function Lattice RG Wilson Precision Tree Exterior Bloch Laurent Pressure Bid Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal InnerProductSpace

variable {G : Gauge} {c f : Side}

/-- Chord divided by absolute t converges at the physical normalization. -/
lemma chord_limit {U : ℝ → G.El} {v : G.Color} (hU : U 0 = 1)
    (hv : HasDerivAt (fun t => G.mat (U t)) (G.colorMat v) 0) :
    Tendsto (fun t => ‖t‖⁻¹ * G.chord (U t)) (𝓝[≠] (0 : ℝ)) (𝓝 ‖v‖) := by
  have hh := hv.tendsto_slope.norm.div_const G.colorScale
  rw [G.colorMat_norm, mul_comm G.colorScale, mul_div_cancel_right₀ _ G.colorScale_pos.ne'] at hh
  simpa only [slope_def_module, sub_zero, hU, G.mat_one, norm_smul, norm_inv,
    Gauge.colorScale, mul_div_assoc, Gauge.chord] using hh

/-- The full box sum (per coarse root i) overcounts port; may count
periodic plaquettes several times. No indicator after this point. -/
lemma port_le (S : StepData c f) (U : Config G f) (i : Site c) :
    port S i U ≤ ∑ z ∈ box (macroR S.patch), ∑ p : PlaqAxes,
      G.chord (faceValue U (wrap f z + S.ratio.embed i, p)) := by
  unfold port Axial.faces Axial.field
  refine Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun p _ => ?_
  unfold Axial.face; split
  · exact le_of_eq (congr_arg G.chord (travel_at ..))
  · exact G.chord_nonneg _

lemma usable_near (S : StepData c f) (x : Dir G f) (k : S.Choices) (i : Site c) :
    ∀ᶠ t : ℝ in 𝓝 0, usable S (represent (t • x)) i k := by
  have h0 : Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 0) := by
    simpa using! (show Continuous fun t : ℝ => t • x from by fun_prop).tendsto 0
  have hmin : ∀ᶠ t : ℝ in 𝓝 0, ∀ y : Site c,
      S.patch.usesMin S.kernel (Push.product S y (t • x)) :=
    eventually_all.mpr fun y => h0.eventually (Push.threshold S y (G := G))
  filter_upwards [hmin] with t ht
  intro y _
  unfold Push.product at ht
  rw [Patch.frameMass, if_pos (show S.patch.usesMin S.kernel _ from ht _)]
  have hp : 0 < Fintype.card S.patch.FrameTag := Fintype.card_pos
  positivity

lemma represent_deriv (x : Dir G f) (e : Bond f) :
    HasDerivAt (fun t : ℝ => G.mat (represent (t • x) e))
      (G.colorMat (collect G x e)) 0 := by
  simpa [linkSum, travel, Step.used, posDir, Step.read] using
    Push.travell [posDir e.2] e.1 x

/-- The slice shell bound (here even just the part for replica of 1) implies
this bound on each fine bond. `x` vanishes on the same tree as in that input. -/
lemma link_bound (S : StepData c f) (h : S.patch.Branches S.kernel G)
    (H : Forest S.ratio) (k : S.Choices) (x : Dir G f)
    (hx : ∀ e ∈ H.trunks, collect G x e = 0)
    (C : ℝ) (hC : 0 ≤ C) (e : Bond f)
    (hcops : ∀ U : Config G f, Stores.SliceSet S H U → usable S U (S.ratio.parent e.1) k →
      Cops (S := S) U 1 (S.prediction U k) e C) :
    ‖collect G x e‖ ≤ C * (∑ z ∈ box (macroR S.patch), ∑ p : PlaqAxes,
      ‖dColor G f 1 x (wrap f z + S.ratio.embed (S.ratio.parent e.1), plaquette p)‖) +
      ‖bills S x (S.ratio.parent e.1, coord e.2)‖ := by
  let U := fun t : ℝ => represent (t • x)
  have hu : U 0 = 1 := by simp [U]
  let i := S.ratio.parent e.1
  let edge : Bond c := (i, e.2)
  let loc := fun z : Cover => wrap f z + S.ratio.embed i
  let X := box (macroR S.patch)
  have he := chord_limit (U := fun t => U t e) (by rw [hu]; rfl) (represent_deriv x e)
  have hp := chord_limit (U := fun t => S.prediction (U t) k edge)
    (by rw [hu]; exact Push.settled S h edge k) (Push.prices S h edge k x)
  have hs (z : Cover) (p : PlaqAxes) :
      Tendsto (fun t => ‖t‖⁻¹ * G.chord (faceValue (U t) (loc z,p)))
        (𝓝[≠] (0 : ℝ)) (𝓝 ‖dColor G f 1 x (loc z, plaquette p)‖) := by
    apply chord_limit
    · unfold U faceValue; rw [zero_smul]; exact Push.stroll_zero _ _
    · rw [← fundamental]; exact Push.travell _ _ _
  have ht : Tendsto (fun t => ∑ z ∈ X, ∑ p : PlaqAxes,
      ‖t‖⁻¹ * G.chord (faceValue (U t) (loc z,p))) (𝓝[≠] (0 : ℝ))
        (𝓝 (∑ z ∈ X, ∑ p : PlaqAxes, ‖dColor G f 1 x (loc z,plaquette p)‖)) := by
    apply tendsto_finsetSum; intro z _; exact tendsto_finsetSum _ fun p _ => hs z p
  apply le_of_tendsto_of_tendsto he ((ht.const_mul C).add hp)
  filter_upwards [(usable_near S x k i).filter_mono nhdsWithin_le_nhds] with t ht'
  have htree : Stores.SliceSet S H (U t) := by
    intro u hub
    change G.lieExp (t • (collect G x u)) * (1:G.El) = _
    rw [hx u hub, smul_zero, G.mat_lieExp_zero, mul_one]
  have ha := hcops (U t) htree ht'
  have ha' : G.chord ((U t) e) ≤ C * port S i (U t) + G.chord (S.prediction (U t) k edge) := by
    unfold Cops at ha
    simp only [replica_one, wire, Pi.one_apply, inv_one, mul_one, one_mul, G.chord_inv] at ha
    split at ha
    · exact ha.trans (add_le_add_right (G.chord_nonneg _) _)
    · exact ha
  change ‖t‖⁻¹ * G.chord ((U t) e) ≤ C * (∑ z ∈ X, ∑ p : PlaqAxes,
    ‖t‖⁻¹ * G.chord (faceValue (U t) (loc z,p))) + ‖t‖⁻¹ * G.chord (S.prediction (U t) k edge)
  have hh := ha'.trans (add_le_add_left (mul_le_mul_of_nonneg_left (port_le S (U t) i) hC) _)
  apply (mul_le_mul_of_nonneg_left hh (show 0 ≤ ‖t‖⁻¹ by positivity)).trans_eq
  simp only [mul_add, mul_left_comm ‖t‖⁻¹ C, Finset.mul_sum, X, loc]

private lemma sum_comp_le {α β : Type*} [Fintype α] [Fintype β] (t : α → β)
    (ht : Injective t) (F : β → ℝ) (hF : ∀ i, 0 ≤ F i) :
    ∑ i, F (t i) ≤ ∑ i, F i := by
  classical
  let m : Finset β := Finset.univ.image t
  calc
    _ = ∑ i ∈ m, F i := by unfold m; rw [Finset.sum_image]; intro i _ j _ e; exact ht e
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ m) fun i _ _ => hF i

lemma sum_parent (g : Ratio c f) (F : Site c → ℝ) :
    ∑ i : Site f, F (g.parent i) = (Fintype.card (Site g.count):ℝ) * ∑ i, F i := by
  calc
    _ = ∑ i : Site c × Site g.count, F i.1 := g.splitSites.sum_comp fun i => F i.1
    _ = _ := by rw [Fintype.sum_prod_type]; simp [Finset.mul_sum]

lemma sum_parent_bond (g : Ratio c f) (F : Bond c → ℝ) :
    ∑ e : Bond f, F (g.parent e.1, e.2) = (Fintype.card (Site g.count):ℝ) * ∑ e, F e := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]; exact sum_parent g (fun i => ∑ j, F (i,j))

private lemma cauchy {α : Type*} (s : Finset α) (F : α → ℝ) :
    (∑ z ∈ s, F z)^2 ≤ (s.card:ℝ) * ∑ z ∈ s, (F z)^2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) F

/-- For each macro-sum square, pay `(box card) * (plaq card)`, and for
its share in the sum over coarse sites pay another `box card`. The latter
comes from injectivity in the *coarse site*, not in the offset. -/
lemma sum_ports_sq (g : Ratio c f) (X : Finset Cover) (F : Body 2 f → ℝ) :
    ∑ i : Site c, (∑ z ∈ X, ∑ p : PlaqAxes, F (wrap f z + g.embed i, plaquette p))^2 ≤
      ((X.card:ℝ) * (Fintype.card PlaqAxes:ℝ)) * ((X.card:ℝ) * ∑ b : Body 2 f, F b ^ 2) := by
  let D (i : Site c) (z : Cover) (p : PlaqAxes) := F (wrap f z + g.embed i, plaquette p)
  let M : ℝ := Fintype.card PlaqAxes
  let N : ℝ := X.card
  have h (i : Site c) : (∑ z ∈ X, ∑ p : PlaqAxes, D i z p)^2 ≤
      (N*M) * ∑ z ∈ X, ∑ p, D i z p ^ 2 := by
    calc
      _ ≤ N * ∑ z ∈ X, (∑ p, D i z p)^2 := cauchy X _
      _ ≤ N * ∑ z ∈ X, (M * ∑ p, D i z p^2) := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z _ => ?_)) (by unfold N; positivity)
        simpa only [M, Finset.card_univ] using cauchy Finset.univ (D i z)
      _ = _ := by rw [← Finset.mul_sum, mul_assoc]
  have ht (z : Cover) : (∑ i, ∑ p, D i z p ^ 2) ≤ ∑ b : Body 2 f, F b^2 := by
    let k (a : Site c × PlaqAxes) : Body 2 f := (wrap f z + g.embed a.1, plaquette a.2)
    have hk : Injective k := by
      intro i j e
      exact Prod.ext (g.embed_injective (add_left_cancel (congr_arg Prod.fst e)))
        (plaqEquiv.injective (congr_arg Prod.snd e))
    have hh := sum_comp_le k hk (fun b => F b ^ 2) (fun _ => sq_nonneg _)
    rw [Fintype.sum_prod_type] at hh
    exact hh
  calc
    _ ≤ ∑ i, (N*M)*(∑ z ∈ X, ∑ p, D i z p^2) := Finset.sum_le_sum fun i _ => h i
    _ = (N*M) * ∑ z ∈ X, ∑ i, ∑ p, D i z p ^ 2 := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (N*M) * ∑ _z ∈ X, ∑ b : Body 2 f, F b ^ 2 := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => ht z)
      unfold N M; positivity
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Coefficients are deliberately after L; count positive-axis bonds only. -/
def curlFactor (L : Side) (X : Finset Cover) (C : ℝ) : ℝ :=
  (2 * C^2) * (Fintype.card (Site L):ℝ) * (Fintype.card Axis:ℝ) *
    ((X.card:ℝ) * (Fintype.card PlaqAxes:ℝ)) * (X.card:ℝ)

def probeFactor (L : Side) : ℝ := 2 * (Fintype.card (Site L):ℝ)

lemma sum_estimate (g : Ratio c f) (X : Finset Cover) (F : Body 2 f → ℝ) (Y : Body 1 c → ℝ)
    (u : Bond f → ℝ) (C : ℝ) (hu : ∀ e, 0 ≤ u e)
    (ht : ∀ e, u e ≤ C * (∑ z ∈ X, ∑ p : PlaqAxes, F (wrap f z + g.embed (g.parent e.1), plaquette p)) +
      Y (g.parent e.1, coord e.2)) :
    ∑ e : Bond f, u e ^ 2 ≤ curlFactor g.count X C * (∑ b, F b ^ 2) +
      probeFactor g.count * (∑ b, Y b ^ 2) := by
  let Z (i : Site c) := ∑ z ∈ X, ∑ p : PlaqAxes, F (wrap f z + g.embed i, plaquette p)
  let Q : ℝ := Fintype.card (Site g.count)
  let m : ℝ := Fintype.card Axis
  have he (e : Bond f) : u e ^ 2 ≤ (2*C^2) * Z (g.parent e.1)^2 + 2*Y (g.parent e.1, coord e.2)^2 := by
    let i := g.parent e.1; let y := Y (i, coord e.2)
    calc
      _ ≤ (C*Z i + y)^2 := pow_le_pow_left₀ (hu _) (ht _) _
      _ ≤ (2*C^2) * Z i ^ 2 + 2*y^2 := by nlinarith only [sq_nonneg (C*Z i - y)]
  have hports : ∑ e : Bond f, Z (g.parent e.1)^2 = Q * (m * ∑ i, Z i ^ 2) := by
    calc
      _ = Q * ∑ e : Bond c, Z e.1 ^ 2 := sum_parent_bond g (fun e => Z e.1 ^ 2)
      _ = Q * (m * ∑ i, Z i ^ 2) := by rw [Fintype.sum_prod_type]; simp [Finset.mul_sum, m]
  have hprobe : ∑ e : Bond f, Y (g.parent e.1, coord e.2)^2 = Q * ∑ b, Y b ^ 2 := by
    have hy : ∑ e : Bond c, Y (e.1, coord e.2)^2 = ∑ b, Y b ^ 2 :=
      (Equiv.prodCongr (Equiv.refl (Site c)) axisEquiv).sum_comp (fun b => Y b ^ 2)
    exact (sum_parent_bond g (fun e => Y (e.1, coord e.2)^2)).trans (congr_arg (Q * ·) hy)
  have hp : (2*C^2)*∑ e : Bond f, Z (g.parent e.1)^2 ≤ curlFactor g.count X C * ∑ b, F b ^ 2 := by
    rw [hports, ← mul_assoc, ← mul_assoc]
    apply (mul_le_mul_of_nonneg_left (sum_ports_sq g X F) ?_).trans_eq
    · unfold curlFactor Q m; simp only [mul_assoc]
    · unfold Q m; positivity
  calc
    _ ≤ ∑ e : Bond f, ((2*C^2)*Z (g.parent e.1)^2 + 2*Y (g.parent e.1, coord e.2)^2) :=
      Finset.sum_le_sum fun i _ => he i
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hprobe, ← mul_assoc 2 Q]
      exact add_le_add_left hp _

section Hessian

/-- On the vertical directions the copied part of stretch vanishes. -/
lemma collect_vertical {S : StepData c f} (H : Forest S.ratio) (v : AxisChart G H) (e : Bond f) :
    collect G (stretch (S:=S) H (0, v)) e = if h : e ∈ H.trunks then 0 else v ⟨e,h⟩ := by
  cases e with | mk u i =>
  have hi : axisEquiv.symm (coord i) = i := axisEquiv.symm_apply_apply _
  simp only [collect, stretch, linearCopy, Pi.zero_apply, hi, ite_self, zero_add]

/-- Coboundary energy including the floor. Counting over all sites and colors. -/
lemma curl_floor {B : Bed} {p : Clip} {a A : ℝ} (h : Floor B p f a A) (x : Dir G f) :
    a * (∑ b, ‖dColor G f 1 x b‖^2) ≤ gaugeFiscal B x x := by
  let F (i : G.ColorIndex) := parts G 1 x i
  let D (i : G.ColorIndex) := d 1 f *ᵥ F i
  have he (i : G.ColorIndex) : dotProduct (F i) (Precision.K (B.metric.acts f) *ᵥ F i) =
      dotProduct (D i) ((B.metric.acts f) *ᵥ D i) := by
    simp only [Precision.K, D, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  have hs : ∑ b, ‖dColor G f 1 x b‖^2 = ∑ i : G.ColorIndex, dotProduct (D i) (D i) := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]; rw [Finset.sum_comm]
    simp only [F, D, dColor, dotProduct, WithLp.ofLp_toLp, pow_two]
  rw [hs, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => ((h.uniform.1 (D i)).1).trans_eq (he i).symm

/-- Restrict the Hessian of the tested germ to the vertical chart. -/
lemma vertical_hessian {S : StepData c f} (H : Forest S.ratio) (k : S.Choices)
    {p : Clip} {W : PathData G} (h : Prismatic H p W) (v : AxisChart G H) :
    iteratedFDeriv ℝ 2 (tested H k p W 0) 0 ![v,v] =
      iteratedFDeriv ℝ 2 (Function.uncurry (tested H k p W)) 0 ![(0,v),(0,v)] := by
  let F := Function.uncurry (tested H k p W)
  let L := ContinuousLinearMap.inr ℝ (Dir G c) (AxisChart G H)
  obtain ⟨s,hs,hF⟩ := (h k).contDiffOn (m := ω) le_rfl (fun _ => rfl)
  obtain ⟨u,hus,hu,h0⟩ := mem_nhds_iff.mp hs
  have ht : IsOpen (L ⁻¹' u) := L.continuous.isOpen_preimage _ hu
  have hv : L 0 ∈ u := by rw [map_zero]; exact h0
  have hf : ContDiffOn ℝ ω F u := hF.mono hus
  have he := L.iteratedFDerivWithin_comp_right hf (hu.uniqueDiffOn) (ht.uniqueDiffOn) hv (i := 2) (by simp)
  rw [iteratedFDerivWithin_of_isOpen _ hu hv, iteratedFDerivWithin_of_isOpen _ ht hv, map_zero] at he
  change iteratedFDeriv ℝ 2 (F ∘ L) 0 _ = _
  rw [he, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

lemma hess_lower {S : StepData c f} (H : Forest S.ratio) (k : S.Choices)
    {B : Bed} {p : Clip} {W : PathData G} {a A : ℝ} (hF : Floor B p f a A)
    (h : Prismatic H p W) (hc : Comptroller H B p W) (v : AxisChart G H) :
    let x := stretch (S:=S) H (0, v)
    a * (∑ b, ‖dColor G f 1 x b‖^2) + S.kernel.penalty * (∑ b, ‖bills S x b‖^2) ≤
      iteratedFDeriv ℝ 2 (tested H k p W 0) 0 ![v,v] := by
  intro x
  rw [vertical_hessian H k h, (hc k).2.2]
  have he : crop (S:=S) H (0,v) = -bills S x := zero_sub _
  rw [he]
  simp only [Pi.neg_apply, real_inner_self_eq_norm_sq, norm_neg]; exact add_le_add_left (curl_floor hF x) _

end Hessian

theorem answer : YM.Bid.F01 := by
  intro hE G L j K a ha
  obtain ⟨C,hC,hcomp⟩ := hE G L j K
  let X := box ((j+3)*L.val + 4*L.val)
  let β := curlFactor L X C
  let γ := probeFactor L
  have hb : 0 ≤ β := by unfold β curlFactor; positivity
  have hh : 0 ≤ γ := by unfold γ probeFactor; positivity
  let η := min a K.penalty / (1+β+γ)
  have hp : 0 < K.penalty := K.penalty_pos
  have hη : 0 < η := div_pos (lt_min ha hp) (by positivity)
  have hprices : η*β ≤ a ∧ η*γ ≤ K.penalty := by
    have he : η*(1+β+γ)=min a K.penalty := div_mul_cancel₀ _ (by positivity)
    constructor
    · exact ((mul_le_mul_of_nonneg_left (show β ≤ 1+β+γ by linarith) hη.le).trans_eq he).trans (min_le_left ..)
    · exact ((mul_le_mul_of_nonneg_left (show γ ≤ 1+β+γ by linarith) hη.le).trans_eq he).trans (min_le_right ..)
  refine ⟨η,hη,?_⟩
  intro c f S hk hl hj hs H B p W A hF hP hc k v
  let x := stretch (S:=S) H (0, v)
  let D := ∑ b, ‖dColor G f 1 x b‖^2
  let Q := ∑ i, ‖bills S x i‖^2
  let u := fun e => ‖collect G x e‖
  have hd : 0 ≤ D := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq : 0 ≤ Q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hX : X = box (macroR S.patch) := by unfold X macroR Patch.radius; rw [hl,hj]
  have hx : ∀ e ∈ H.trunks, collect G x e = 0 := fun e he => (collect_vertical H v e).trans (dif_pos he)
  have hall : ∑ e : Bond f, u e ^ 2 ≤ β*D + γ*Q := by
    have hw : L = S.ratio.count := hl.symm
    have hL := fun e => link_bound S hs.1 H k x hx C hC.le e
      (fun U hu hv => hcomp c f S hk hl hj hs.2.1 hs.2.2 H U hu 1 e k hv)
    change _ ≤ curlFactor L X C * D + probeFactor L * Q
    rw [hX, hw]
    exact sum_estimate S.ratio _ (fun b => ‖dColor G f 1 x b‖) (fun b => ‖bills S x b‖) u C
      (fun e => norm_nonneg _) hL
  have hm : ∑ i : H.Free, ‖v i‖^2 ≤ ∑ e : Bond f, u e ^ 2 := by
    have he (i : H.Free) : u i.val = ‖v i‖ := by
      change ‖collect G (stretch (S:=S) H (0,v)) _‖ = _
      rw [collect_vertical, dif_neg i.property]
    simp_rw [← he]
    exact sum_comp_le (fun i : H.Free => i.val) Subtype.val_injective (fun i => u i ^ 2) (fun i => sq_nonneg _)
  apply (mul_le_mul_of_nonneg_left (hm.trans hall) hη.le).trans
  have Hh : a*D + K.penalty*Q ≤ iteratedFDeriv ℝ 2 (tested H k p W 0) 0 ![v,v] := by
    rw [← hk]; exact hess_lower H k hF hP hc v
  apply le_trans ?_ Hh
  rw [mul_add, ← mul_assoc, ← mul_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_right hprices.1 hd) (mul_le_mul_of_nonneg_right hprices.2 hq)

end YM.Work.F01
