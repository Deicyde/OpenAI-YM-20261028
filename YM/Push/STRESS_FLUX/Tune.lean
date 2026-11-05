import YM.Bid.Station
import YM.Push.STRESS_FLUX.Matching
import YM.Work.A01.Conserve
import YM.Work.A01.Mirror
import YM.Work.A15.Shell

/-!
Pure interface consequences: transform a stress already giving the two flux
laws (for use on the free comparator only). Compensated compact rotation
average is from Work.A15, then take real part and remove a scalar *identity*
tensor (not the total curvature square). -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Tune
open Table Work.A01 Work.A15 Function Set Filter MeasureTheory Analysis
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} {n d : ℕ} {W : DiffPlan S} {H : S.RealSpin} {X : S.Rotation} {J : S.Stress}
    {P : Climb.Parts S} {A : Ward.SpinRows S} {x : Points (n+1)} {χ : E4 → ℝ}

lemma laws_smul (hs : S.Smooth) (h : StressLaws S J P A) (t : ℝ) : StressLaws S (t • J) (t • P) (t • A) where
  translation {n x} hx q {_χ} hw b d B := by
    rw [← translationFlux_apply hx hw hs, RCLike.real_smul_eq_coe_smul (K:=ℂ) t J,map_smul,translationFlux_apply,h.translation hx q hw, ← front_eval, ← map_smul]
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) t P]; exact front_eval ..
  rotation {n x} hx q {_χ} hw b d B := by
    change _ = S.useAt S x (Fin.cons ⟨d,t • A d b B⟩ q)
    rw [← angularFlux_apply hx hw hs, RCLike.real_smul_eq_coe_smul (K:=ℂ) t J,map_smul,angularFlux_apply,h.rotation hx q hw, ← front_eval, ← map_smul]
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) t (A d b B)]; exact front_eval ..

lemma lie_real (h : X.Laws W H) (d : ℕ) (u : Ortho.Skew) (x : S.Field d) :
    S.conj H d (X.lie d u x) = X.lie d u (S.conj H d x) := by
  let m : S.Field d →L[ℝ] S.Field d := {
    toFun := S.conj H d
    map_add' := map_add _
    map_smul' r v := by change S.conj H d (r • v) = r • S.conj H d v; simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smulₛₗ]; simp
    cont := Spin.cont_conj H d }
  have he : HasDerivAt (fun t => S.conj H d (X.act d (Ortho.oneParameter u t) x)) (S.conj H d (X.lie d u x)) (0:ℝ) :=
    m.hasFDerivAt.comp_hasDerivAt 0 (h.infinitesimal d u x)
  simp_rw [h.real] at he
  exact he.unique (h.infinitesimal d u _)

def conjugate (H : S.RealSpin) (J : S.Stress) : S.Stress := fun a b => S.conj H 4 (J a b)

def re (H : S.RealSpin) (J : S.Stress) := (2:ℝ)⁻¹ • (J + conjugate H J)

lemma torque_real (h : S.Symmetric) (H : S.RealSpin) (J : S.Stress) (q : Fin n → S.Tag) (B : S.Field d)
    (V : E4 → E4) (hx : x∈conf _) (hw : Window x χ) :
    star (flux J χ V x (realTag H ∘ q) (S.conj H d B)) = flux (conjugate H J) χ V x q B := by
  have hq : realTag H ∘ (realTag H ∘ q) = q := funext fun i => by change Sigma.mk (q i).1 (S.conj H _ (S.conj H _ _)) = _; rw [reflect_star]
  have he a b y : term (conjugate H J) χ V x q B a b y = star (term J χ V x (realTag H ∘ q) (S.conj H d B) a b y) := by
    by_cases he : D (basis a) χ y = 0
    · simp [term,he]
    rw [term,term,star_mul',← real_eval h H (separated_of_D hx hw he),comp_cons,comp_cons,hq,conjugate]
    congr 1
    · simp
    congr 2
    exact congr_arg₂ _ ((congr_arg (Sigma.mk d) (S.reflect_star H d B)).symm) rfl
  simp_rw [flux,he,star_neg,star_sum,Complex.star_def,integral_conj]

lemma re_laws (hs : S.Hierarchy) (hW : W.Orientation hs.spin) (hX : X.Laws W hs.spin) (hp : StressLaws S J W.deriv X.lie) :
    StressLaws S (re hs.spin J) W.deriv X.lie := by
  have he (F : S.Stress →ₗ[ℂ] ℂ) : F J = F (conjugate hs.spin J) → F (re hs.spin J) = F J := by
    intro hh
    change F.restrictScalars ℝ ((2:ℝ)⁻¹ • (J + conjugate hs.spin J)) = _
    rw [map_smul]
    change (2:ℝ)⁻¹ • F (J + conjugate hs.spin J) = _
    rw [map_add,← hh,Complex.real_smul]; push_cast; ring
  have hr {d n : ℕ} (v : S.Field d) (q : Fin n → S.Tag) {x : Points (n+1)} (hx : x ∈ conf _) :
      S.useAt S x (Fin.cons ⟨d,v⟩ q) = star (S.useAt S x (Fin.cons ⟨d,S.conj hs.spin d v⟩ (realTag hs.spin ∘ q))) := by
    rw [show Fin.cons (α:=fun _ => S.Tag) ⟨d,S.conj hs.spin d v⟩ (realTag hs.spin ∘ q) = _ from (comp_cons (realTag hs.spin) (⟨d,v⟩ : S.Tag) q).symm,
      real_eval hs.laws.toSymmetric hs.spin hx,star_star]
  constructor
  · intro n x hx q χ hw b d B
    rw [← hp.translation hx q hw, ← translationFlux_apply hx hw hs.smooth,← translationFlux_apply hx hw hs.smooth]
    apply he
    rw [translationFlux_apply,translationFlux_apply, ← flux_translation (conjugate hs.spin J),
      ← torque_real hs.laws.toSymmetric hs.spin J q B _ hx hw,flux_translation, hp.translation hx q hw, hp.translation hx _ hw,← hW.realDer]; exact hr _ _ hx
  intro n x hx q χ hw g d B
  rw [← hp.rotation hx q hw, ← angularFlux_apply hx hw hs.smooth,← angularFlux_apply hx hw hs.smooth]
  apply he
  rw [angularFlux_apply,angularFlux_apply, ← flux_spin, ← flux_spin, ← torque_real hs.laws.toSymmetric hs.spin J q B _ hx hw,flux_spin,flux_spin,hp.rotation hx q hw,hp.rotation hx _ hw,← lie_real hX]; exact hr _ _ hx

lemma re_tensor (hs : S.Hierarchy) (hX : X.Laws W hs.spin) (hJ : Tensorial X J) : Tensorial X (re hs.spin J) := by
  intro K a b
  unfold re
  change X.act _ _ ((2:ℝ)⁻¹ • (J a b + S.conj hs.spin 4 (J a b))) = ∑ i : Axis, ∑ j : Axis, (↑(_ : ℝ):ℂ) • ((2:ℝ)⁻¹ • (J i j + S.conj hs.spin 4 (J i j)))
  rw [show X.act _ _ ((2:ℝ)⁻¹ • _) = (2:ℝ)⁻¹ • X.act 4 K (J a b + S.conj hs.spin 4 (J a b)) from ((X.act 4 K).toLinearMap.restrictScalars ℝ).map_smul _ _,map_add,← hX.real,hJ,map_sum]
  simp [map_sum,map_smulₛₗ,smul_add,Finset.sum_add_distrib,smul_comm (_:ℂ) ((2:ℝ)⁻¹), Finset.smul_sum]

lemma re_conj (H : S.RealSpin) (J : S.Stress) a b : S.conj H 4 (re H J a b) = re H J a b := by
  unfold re
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  simp [conjugate,map_smulₛₗ, reflect_star, add_comm,map_ofNat]

def vac (S : Table L) (t : ℝ) : S.Stress := fun a b => if a=b then t • S.unit 4 else 0
lemma vac_flux (hs : S.Hierarchy) (q : Fin n → S.Tag) (B : S.Field d) (hx : x∈conf _) (hw : Window x χ) (r : ℝ)
    (V : E4 → E4) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun y => V y b)) (hk : killing V) : flux (vac S r) χ V x q B = 0 := by
  let q' := Fin.cons (α:=fun _ => S.Tag) ⟨d,B⟩ q
  have he a b y : term (vac S r) χ V x q B a b y = if a=b then ((r*S.useAt S x q') * ↑(D (basis a) χ y * V y a)) else 0 := by
    unfold term
    by_cases hh : D (basis a) χ y=0
    · simp [hh]
    have hy := separated_of_D hx hw hh
    rw [← front_eval, vac]
    split_ifs with ht
    · subst b
      rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,front_eval, S.at_unit hs.laws hy q',show Points.tail (Points.cons y x) = x from rfl,smul_eq_mul]; change _ * (↑r * S.useAt S x q') = _; ring
    rw [map_zero, mul_zero]
  have h0 (a : Axis) : (∫ y : E4, (↑(D (basis a) χ y * V y a):ℂ)) = 0 := by
    let F (y : E4) := (V y a : ℂ)
    have hF : ContDiff ℝ ∞ F := Complex.ofRealCLM.contDiff.comp (hv a)
    have hd y : D (basis a) F y = 0 := by
      change fderiv ℝ (Complex.ofRealCLM ∘ (fun y => V y a)) y (basis a) = _
      rw [fderiv_comp y Complex.ofRealCLM.differentiableAt ((hv a).differentiable (by simp) _), Complex.ofRealCLM.fderiv, ContinuousLinearMap.comp_apply]
      exact congr_arg Complex.ofReal (show D (basis a) (fun y => V y a) y = 0 by linarith [hk a a y]) |>.trans Complex.ofReal_zero
    have ht : -(∫ y : E4, D (basis a) χ y • F y) = ∫ y : E4, χ y • D (basis a) F y := Eq.symm (integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
        (cutoff_integrable (hw.2.1.fderiv_apply ℝ (basis a)) ((hw.1.continuous_fderiv (by simp)).clm_apply continuous_const) (fun _ _ => hF.continuous.continuousAt))
        (cutoff_integrable hw.2.1 hw.1.continuous (fun _ _ => ((hF.continuous_fderiv (by simp)).clm_apply continuous_const).continuousAt))
        (cutoff_integrable hw.2.1 hw.1.continuous (fun _ _ => hF.continuous.continuousAt)) (fun y _ => hw.1.differentiable (by simp) y) (fun y _ => hF.differentiable (by simp) y))
    simpa only [F, hd,smul_zero,integral_zero, neg_eq_zero,Complex.real_smul, ← Complex.ofReal_mul] using ht
  simp only [flux,neg_eq_zero]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _) (fun b _ hb => ?_)]
  · simp only [he,ite_true,integral_const_mul,h0,mul_zero]
  · simp [he,hb.symm]

lemma vac_laws (hs : S.Hierarchy) (h : StressLaws S J P A) (r : ℝ) : StressLaws S (J - vac S r) P A := by
  constructor
  · intro n x hx q χ hw b d B
    rw [← translationFlux_apply hx hw hs.smooth,map_sub,translationFlux_apply,translationFlux_apply, ← flux_translation (vac S r),
      vac_flux hs _ _ hx hw r _ (fun _ => contDiff_const) (killing_const _),sub_zero,h.translation hx q hw]
  intro n x hx q χ hw g d B
  rw [← angularFlux_apply hx hw hs.smooth,map_sub,angularFlux_apply,angularFlux_apply, ← flux_spin (vac S r),
    show flux _ _ (fun y => M4.move g.val (y - x 0)) x q B=0 from vac_flux hs _ _ hx hw r _ (smooth_orbital g (x 0)) (killing_orbital _ _),sub_zero,h.rotation hx q hw]
end YM.StressFlux.Tune
