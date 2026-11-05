import YM.Extra.WEAK_SCALING_ACTLAW.Fit
import YM.Next.EXTRACTION.Base

/-!
# Fixed finite-dimensional adjustment to *exact* compatible maps

Split free inclusions by fixed equivariant projections before using the
comparison columns. No point, test, direction or configuration-dependent
change of basis. Prove near identity in the weak coordinates and retain all
finite systems and derivative fits at the station. Even `Scaling.U` above
the requested cap must be an equivalence (pole unrelated to this station
suffices there).
-/
set_option maxHeartbeats 400000
set_option autoImplicit false
noncomputable section
namespace YM.Extra.WeakScaling
open Set Function Filter Table Climb
open scoped Topology ContDiff
variable {G : Gauge} {L : Register G} {T : Table L} {d D : ℕ}

private abbrev next (d : ℕ) := Nat.le_succ d
private def conjugated (h : T.RealSpin) (f : T.Field (d+1) →ₗ[ℂ] T.Field d) : T.Field (d+1) →ₗ[ℂ] T.Field d :=
    ((T.conj h d).comp f).comp (T.conj h _)
private def averaged (h : T.RealSpin) (f : T.Field (d+1) →ₗ[ℂ] T.Field d) :=
    (Fintype.card Signed : ℂ)⁻¹ • ∑ s : Signed, (T.mirror h d s⁻¹).comp (f.comp (T.mirror h _ s))
private lemma averaged_cov (h : T.RealSpin) (f : T.Field (d+1) →ₗ[ℂ] T.Field d) (g : Signed) v :
    averaged h f (T.mirror h _ g v) = T.mirror h _ g (averaged h f v) := by
  simp only [averaged,LinearMap.smul_apply,map_smul,LinearMap.sum_apply,LinearMap.comp_apply,map_sum]
  refine congrArg (fun x : T.Field d => (Fintype.card Signed:ℂ)⁻¹ • x) ?_
  apply Fintype.sum_equiv (Equiv.mulRight g); intro s
  rw [show (Equiv.mulRight g) s = s*g from rfl, ← T.mirror_mul, ← T.mirror_mul, mul_inv_rev, mul_inv_cancel_left]

/-- H-equivariant, real retraction of each free rise map (works more generally). -/
lemma retraction (H : T.Hierarchy) (W : DiffPlan T) (h : W.Inclusions T) (he : W.Orientation H.spin) (d : ℕ) :
    ∃ P : T.Field (d+1) →ₗ[ℂ] T.Field d, (∀ v, P (W.rise (next d) v) = v) ∧
      (∀ g v, P (T.mirror H.spin _ g v) = T.mirror H.spin _ g (P v)) ∧ ∀ v, P (T.conj H.spin _ v) = T.conj H.spin _ (P v) := by
  obtain ⟨R,hR⟩ := (W.rise (next d)).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr
    (W.inject H.laws.toSymmetric h _))
  have hr v : R (W.rise (next d) v) = v := LinearMap.congr_fun hR v
  let Q := averaged H.spin R
  have hc : (Fintype.card Signed : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hQ v : Q (W.rise (next d) v) = v := by
    simp only [Q,averaged,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,he.mirrorInc,hr,
      ← T.mirror_mul,inv_mul_cancel,T.mirror_one, Finset.sum_const,Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ,inv_smul_smul₀ hc]
  let P := conjugated H.spin Q
  have hP v : P (W.rise (next d) v) = v := by
    dsimp only [P,conjugated,LinearMap.comp_apply]; rw [he.realInc,hQ,T.reflect_star]
  refine ⟨(2:ℂ)⁻¹ • (Q+P),fun v => ?_, fun g v => ?_,fun v => ?_⟩
  · simp [hQ,hP,← two_smul ℂ]
  · simp only [Q,P,LinearMap.smul_apply,map_smul,LinearMap.add_apply,map_add,conjugated,LinearMap.comp_apply,
      averaged_cov,T.mirror_star]
  simp only [LinearMap.smul_apply,map_smulₛₗ,LinearMap.add_apply,map_add,P,conjugated,LinearMap.comp_apply,
    T.reflect_star,map_inv₀,map_ofNat,add_comm]

variable {C : Family G} {S : Table C.book}

/-- Adjacent entries commute exactly after the adjustment, *not* an
assumption that the original comparison choices commute. -/
def adjusted (V : DiffPlan S) (W : DiffPlan (Free C))
    (P : ∀ d, (Free C).Field (d+1) →ₗ[ℂ] (Free C).Field d) (A : ∀ d, YM.Spin.change S d) :
      ∀ d, (Free C).Field d →ₗ[ℂ] S.Field d
  | 0 => (A 0).toLinearMap
  | d+1 => (V.rise (next d)).comp ((adjusted V W P A d).comp (P d)) +
    (A (d+1)).toLinearMap.comp (LinearMap.id - (W.rise (next d)).comp (P d))

variable {V : DiffPlan S} {W : DiffPlan (Free C)}
    {P : ∀ d, (Free C).Field (d+1) →ₗ[ℂ] (Free C).Field d}
    {A : ∀ d, YM.Spin.change S d} {h : S.Hierarchy} {H : (Free C).Hierarchy}

def Exact (V : DiffPlan S) (W : DiffPlan (Free C)) (h : S.RealSpin) (H : (Free C).RealSpin)
    (X : ∀ d, (Free C).Field d →ₗ[ℂ] S.Field d) (D : ℕ) :=
    (∀ d ≤ D, (∀ g v, X d ((Free C).mirror H d g v)=S.mirror h d g (X d v)) ∧
      (∀ v, X d ((Free C).conj H d v)=S.conj h d (X d v)) ∧ X d ((Free C).unit d)=S.unit d) ∧
    ∀ d e (he : d ≤ e), e ≤ D → ∀ v, X e (W.rise he v) = V.rise he (X d v)

lemma adjusted_succ (d : ℕ) (v : (Free C).Field (d+1)) :
    adjusted V W P A (d+1) v = V.rise (next d) (adjusted V W P A d (P d v)) + A (d+1) (v-W.rise (next d) (P d v)) := rfl
lemma adjusted_exact (hf : V.Inclusions S) (hg : W.Inclusions (Free C)) (hv : V.Orientation h.spin) (hw : W.Orientation H.spin)
    (hr : ∀ d, (∀ v, P d (W.rise (next d) v)=v) ∧
      (∀ g v, P d ((Free C).mirror H.spin _ g v) = (Free C).mirror H.spin _ g (P d v)) ∧
      ∀ v, P d ((Free C).conj H.spin _ v) = (Free C).conj H.spin _ (P d v))
    (ha : ∀ d ≤ D, YM.Spin.realH h.spin H.spin (A d) ∧ A d ((Free C).unit d)=S.unit d) :
    Exact V W h.spin H.spin (adjusted V W P A) D := by
  let X := adjusted V W P A
  have he d v : X (d+1) (W.rise (next d) v) = V.rise (next d) (X d v) := by
    simp only [X,adjusted_succ,(hr d).1,sub_self,map_zero,add_zero]
  constructor
  · intro d hd; induction d with
    | zero => exact ⟨(ha 0 hd).1.1,(ha 0 hd).1.2,(ha 0 hd).2⟩
    | succ d ih =>
      obtain ⟨h₁,h₂,h₃⟩ := ih (by omega)
      refine ⟨fun g v => ?_,fun v => ?_,?_⟩
      · rw [adjusted_succ,(hr d).2.1,h₁, ← hw.mirrorInc,← map_sub,(ha _ hd).1.1, adjusted_succ,map_add,hv.mirrorInc]
      · rw [adjusted_succ,(hr d).2.2,h₂,← hw.realInc,← map_sub,(ha _ hd).1.2, adjusted_succ,map_add,hv.realInc]
      change X _ _=_; rw [← W.fixs hg H.laws (next d),he,h₃,V.fixs hf h.laws]
  intro d e hde _ v
  change X e _ = _
  induction e, hde using Nat.le_induction with
  | base => rw [W.arrival H.laws.toSymmetric hg,V.arrival h.laws.toSymmetric hf]
  | succ e hde ih => rw [← W.transit H.laws.toSymmetric hg hde (next e),he,ih (by omega),V.transit h.laws.toSymmetric hf]

variable {A' : ℕ → ∀ d, YM.Spin.change S d}

def perturb (V : DiffPlan S) (W : DiffPlan (Free C)) (P : ∀ d, (Free C).Field (d+1) →ₗ[ℂ] (Free C).Field d)
    (A' : ℕ → ∀ d, YM.Spin.change S d) (d k : ℕ) :=
  (A' k d).symm.toLinearMap.comp (adjusted V W P (A' k) d)

def Near (V : DiffPlan S) (W : DiffPlan (Free C)) (A' : ℕ → ∀ d, YM.Spin.change S d) (D : ℕ) :=
    ∀ d, d < D → ∀ v, Tendsto (fun k => (A' k (d+1)).symm (V.rise (next d) (A' k d v))) atTop (𝓝 (W.rise (next d) v))

lemma perturb_limit (h : Near V W A' D) (hd : d≤D) (v : (Free C).Field d) :
    Tendsto (fun k => perturb V W P A' d k v) atTop (𝓝 v) := by
  induction d with
  | zero =>
    have he k : perturb V W P A' 0 k v = v := LinearEquiv.symm_apply_apply ..
    simp [he]
  | succ d ih =>
    let F (k : ℕ) := (A' k (d+1)).symm.toLinearMap.comp ((V.rise (next d)).comp (A' k d).toLinearMap)
    have he := Dash.fit_plane F (W.rise (next d)) (h d hd)
    have hi (k : ℕ) : perturb V W P A' (d+1) k v = F k (perturb V W P A' d k (P d v)) + (v-W.rise (next d) (P d v)) := by
      simp only [perturb,F,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
        adjusted_succ,map_add,LinearEquiv.symm_apply_apply]
    have ht := Dash.arcing he (ih (by omega) (P d v))
    change Tendsto (fun i => F i _) _ (𝓝 (W.rise (next d) _)) at ht
    simp_rw [hi]
    convert ht.add_const (v-W.rise (next d) (P d v)) using 2
    abel

lemma eventually_unit (h : Near V W A' D) (hd : d ≤ D) : ∀ᶠ k in atTop, Bijective (adjusted V W P (A' k) d) := by
  have ht := Dash.fit_plane (perturb V W P A' d) LinearMap.id (perturb_limit h hd)
  filter_upwards [ht.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds (show _ from injective_id))] with k hk
  have he : Injective (adjusted V W P (A' k) d) := Injective.of_comp (f := (A' k d).symm) hk
  exact ⟨he,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ((A' k d).finrank_eq)).1 he⟩

open scoped Classical in
def rotateChart (V : DiffPlan S) (W : DiffPlan (Free C)) (P : ∀ d, (Free C).Field (d+1) →ₗ[ℂ] (Free C).Field d)
    (A' : ℕ → ∀ d, YM.Spin.change S d) (k d : ℕ) :=
  if h : Bijective (adjusted V W P (A' k) d) then LinearEquiv.ofBijective _ h else A' k d

lemma rotate_eq {k : ℕ} (h : Bijective (adjusted V W P (A' k) d)) (v) :
    rotateChart V W P A' k d v = adjusted V W P (A' k) d v := by rw [rotateChart,dif_pos h]; rfl
lemma relative (h : Near V W A' D) (hd : d ≤ D) (v : (Free C).Field d) :
    Tendsto (fun k => (A' k d).symm (rotateChart V W P A' k d v)) atTop (𝓝 v) := by
  apply (perturb_limit (P:=P) h hd v).congr'
  filter_upwards [eventually_unit (P:=P) h hd] with k hk
  rw [rotate_eq hk]; rfl

/-- Conjugations of scaled linear maps through the new chart have the same
limits. Applies e.g. to r*V.deriv and there is no orthogonality assumption
on the maps or their corrections. -/
lemma transformed {e : ℕ} {F : ℕ → ∀ d, YM.Spin.change S d}
    (m : ℕ → S.Field d →ₗ[ℂ] S.Field e) (g : (Free C).Field d →ₗ[ℂ] (Free C).Field e)
    (hm : ∀ v, Tendsto (fun k => (A' k e).symm (m k (A' k d v))) atTop (𝓝 (g v)))
    (hd : ∀ v, Tendsto (fun k => (A' k d).symm (F k d v)) atTop (𝓝 v))
    (he : ∀ v, Tendsto (fun k => (A' k e).symm (F k e v)) atTop (𝓝 v)) (v : (Free C).Field d) :
    Tendsto (fun k => (F k e).symm (m k (F k d v))) atTop (𝓝 (g v)) := by
  let M k := (A' k e).symm.toLinearMap.comp ((m k).comp (A' k d).toLinearMap)
  let a k := (A' k e).symm.toLinearMap.comp (F k e).toLinearMap
  have ht := Dash.fit_plane M g hm
  apply Work.A04.tendsto_of_fitted a (LinearMap.id : (Free C).Field e →ₗ[ℂ] (Free C).Field e) injective_id he
  have hh := Dash.arcing ht (hd v)
  apply hh.congr'
  refine Eventually.of_forall fun k => ?_
  change (A' k e).symm (m k (A' k d ((A' k d).symm (F k d v)))) = (A' k e).symm (F k e ((F k e).symm (m k _)))
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

variable {f : Extraction.Order} (s : Spec.Seed C f S)

def Graded (V : DiffPlan S) (W : DiffPlan (Free C)) (h : S.RealSpin) (H : (Free C).RealSpin)
    (X : ∀ d, YM.Spin.change S d) (D : ℕ) := Exact V W h H (fun d => (X d).toLinearMap) D

lemma repaired {M D' : ℕ} {Q : ℝ} (b : Survey S s.kernel.spin H.spin M D' Q)
    (hF : ∀ d, Nonempty (YM.Spin.change S d)) (hD : D ≤ D') (hw : ∀ d ≤ D, Equipped H d M D' Q)
    (hi : V.Inclusions S) (hi' : W.Inclusions (Free C)) (hp : V.Derivatives S) (hp' : W.Derivatives (Free C))
    (hv : V.Orientation s.kernel.spin) (hv' : W.Orientation H.spin) :
    ∃ X : ℕ → ∀ d, YM.Spin.change S d,
      (∀ᶠ k in atTop, Graded V W s.kernel.spin H.spin (X k) D) ∧
      (∀ d, d < D → ∀ a v, Tendsto (fun k => (X k (d+1)).symm (b.r k • V.deriv d a (X k d v))) atTop (𝓝 (W.deriv d a v))) ∧
      (∀ᶠ k in atTop, ∀ d ≤ D, ∀ v, b.charts hF k d v = b.U k d v) ∧
      ∀ d ≤ D, ∀ v, Tendsto (fun k => (b.charts hF k d).symm (X k d v)) atTop (𝓝 v) := by
  choose P h₁ h₂ h₃ using retraction H W hi' hv'
  let A := b.charts hF
  let X := rotateChart V W P A
  have he : Near V W A D := fun d hd => b.inc_limit s hF V W hi hi' _ (by omega) (hw _ hd) (hw d hd.le)
  have ht : ∀ᶠ k in atTop, ∀ d ≤ D, ∀ v, A k d v = b.U k d v := by
    have hh (d) (hd : d ∈ Finset.Iic D) := b.eventually_bijective s ((Finset.mem_Iic.mp hd).trans hD) (hw d (Finset.mem_Iic.mp hd))
    filter_upwards [((eventually_all_finset _).mpr hh)] with k hk d hd v
    exact b.equals hF (hk d (Finset.mem_Iic.mpr hd)) v
  refine ⟨X, ?_, fun d hd a => transformed (F:=X) (A':=A) (fun k => b.r k • V.deriv d a) _
    (b.deriv_limit s hF V W hp hp' (by omega) (hw _ hd) (hw d hd.le) · a) (relative (P:=P) he hd.le) (relative (P:=P) he hd), ht, fun d hd => relative (P:=P) he hd⟩
  have hh (d) (hd : d∈Finset.Iic D) := eventually_unit (P:=P) he (Finset.mem_Iic.mp hd)
  filter_upwards [(eventually_all_finset _).mpr hh,ht] with k hk ht
  have hy d (hd : d≤D) := rotate_eq (hk d (Finset.mem_Iic.mpr hd))
  have ha d (hd : d ≤ D) : YM.Spin.realH s.kernel.spin H.spin (A k d) ∧ A k d ((Free C).unit d)=S.unit d := by
    unfold YM.Spin.realH
    simp_rw [ht d hd]; exact ⟨⟨b.mirror k d (by omega),b.conj k d (by omega)⟩,b.unit k d (by omega)⟩
  obtain ⟨l,h⟩ := adjusted_exact (h:=s.kernel) (H:=H) hi hi' hv hv' (fun d => ⟨h₁ d,h₂ d,h₃ d⟩) ha
  constructor
  · intro d hd; dsimp only [X,LinearEquiv.coe_coe]; simp_rw [hy d hd]; exact l d hd
  intro d e hb hd; dsimp only [X,LinearEquiv.coe_coe]; simp_rw [hy d (hb.trans hd),hy e hd]; exact h d e hb hd
end YM.Extra.WeakScaling
