import YM.RG08.Canon.Waves
import YM.RG08.Action.History
/-! # Recorded link-port Jet dictionary. Pay logarithmic terms only on loop:
difference at any fixed period by Paid Kin. On symbols equality via cover. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect Bloch UVExt.Paths
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {F : Forest S.ratio} {p q : Clip} {R T : PathData G} {σ M Λ : ℝ} {ρ : fieldDir G c 1 → AxisChart G F} {D : ChartRatio G} {Q : Pot G 2} {Z : Air G}
lemma innate {V H : fieldDir G c 1→ℝ} {j : ℕ}(h : SameJet j V H) : Tensor.coeff (V∘arm G c 1) j 0=Tensor.coeff (H∘arm G c 1) j 0 := by
  unfold Tensor.coeff; congr 1
  let K:= (arm G c 1).toContinuousLinearMap
  ext1 v; change iteratedFDeriv ℝ j (V ∘ K) _ _=iteratedFDeriv ℝ j (H ∘ K) _ _
  rw [wired K (by rw [map_zero]; exact h.1.analyticAt),wired K (by rw [map_zero]; exact h.2.1.analyticAt),map_zero,h.2.2]
lemma antique (h : ShellC F p R ρ D Q Z) (hp : ClassicalMatch F p q R T ρ) (j : ℕ)(hj:j≤4) : Tensor.coeff (classicFn q T (f:=c)) j 0= recital (sector Q Z 0 j) c := by
  let t:S.Choices:=Classical.arbitrary _; rw [← h.start j hj t]; exact (innate (hp j hj t)).symm

lemma cents_tax {α Θ A K : ℝ} (t:S.Choices)(hc : FiniteBound F R T p q α D ρ Θ A K) (hp : 0≤Θ)(hk : 0≤K) : aperture (cents c*(4*Θ*K*Real.exp (-A*c.val))) (draft α T q ∘ arm G c 1) (aureole R F t p ρ D) 1 := by
  let ε:= (Fintype.card (Site c) : ℝ)*Θ*K* Real.exp (-A*c.val); let g:=thermal F t p R ρ D
  let L:= arm G c 1; let X:=g ∘ L
  have hv : ContDiffAt ℝ ω X 0:= (show ContDiffAt ℝ ω g (L 0) by rw [map_zero]; exact hc.born t).comp _ L.contDiff.contDiffAt
  have hz : ContDiffAt ℝ ω (draft α T q ∘ arm G c 1) 0 := (show ContDiffAt ℝ ω (draft (c:=c) α T q) (L 0) by rw [map_zero]; exact hc.classicalResult).comp _ L.contDiff.contDiffAt
  rw [show cents c*(4*Θ*K*Real.exp ..)= 4*ε by unfold cents ε; ring]
  apply priced_wave (by unfold ε; positivity); intro i j u v hu he
  have hQ := hc.wave_price t i j u v hu he
  rw [show aureole R F t p ρ D=X-(fun _=> g 0) from rfl,iteratedFDeriv_sub_apply (hv.of_le le_top) contDiffAt_const,show iteratedFDeriv ℝ 2 (fun _ : Link G c=>g 0)=_ from iteratedFDeriv_succ_const (𝕜:=ℝ) 1 (g 0)];
  simp only [Pi.zero_apply, sub_zero]; rw [← wired_wave (f:=g) hv, ← wired_wave hz]; exact hQ

-- Analytic all-P simultaneous at same R. Output symbol unchanged by real path shifts.
def cartography (G:Gauge)(V:∀ m:Side,Link G m→ℝ)(j:ℕ):Prop:= ∃ (Y:Picture G j) (w C:ℝ), (∀ i k,Firm w C (Y i k)) ∧ ∀ m,Recorded Y (V m) 0
lemma cart_join {j : ℕ}{A B:∀ m:Side, Link G m→ℝ}(h:cartography G A j)(hp : cartography G B j)(ha : ∀ m, AnalyticAt ℝ (A m) 0)(hb:∀ m,AnalyticAt ℝ (B m) 0) :cartography G (A+B) j:= by
  obtain ⟨Y,w,C,hY,h⟩:=h; obtain ⟨Z,u,D,H,hp⟩:=hp
  exact ⟨Y+Z,min w u,C+D,fun i j=> (Firm.add (f:=Y i j) ((hY i j).mono (lt_min (hY i j).width_pos (H i j).width_pos) (min_le_left ..) le_rfl) ((H i j).mono (lt_min (hY i j).width_pos (H i j).width_pos) (min_le_right ..) le_rfl)),fun m=>(h m).both (ha m) (hb m) (hp m)⟩
lemma cart_base (j : ℕ) (h : R.Bounds p σ M Λ): cartography G (fun m=> inputSeries p R (m:=m)) j := by
  obtain ⟨η,A,hy,he,H⟩:= column_price G j (σ:=σ) M p.direct h.width p.quadratic_pos.le
  obtain ⟨hv,L,hp,hh⟩:=H p R _ _ _ le_rfl h h.rows; exact ⟨L,η,A,hp,hh⟩
lemma cart_path {n : ℕ}(j:ℕ)(p:ℕ → Atom G n) (h : 0<σ) (hp : SumBudget (fun i=> (p i).budget σ) M): cartography G (fun m=> turnSeries p (m:=m)) j:= by
  obtain ⟨w,C,hq,hE,H⟩:=orbit_cost G n j h
  obtain ⟨P,hP,hz⟩:= H p M hp; exact ⟨P,w,M*C,hP,hz⟩
lemma cart_map (j : ℕ)(h : R.Bounds p σ M Λ) : cartography G (fun m=> classicFn p R (f:=m)) j := by
  change cartography G (fun m=> intended p R (m:=m)) j
  simp_rw [intent]
  exact cart_join (A:= (fun m=> inputSeries p R (m:=m)+turnSeries R.cubic)) (cart_join (cart_base j h) (cart_path j R.cubic h.width h.three) (fun m=> (stain_knit _ _ h).analytic) (fun m=> turns_analytic _ h.width h.three)) (cart_path j R.quartic h.width h.four) (fun m=> (stain_knit _ _ h).analytic.add (turns_analytic _ h.width h.three)) (fun m=> turns_analytic _ h.width h.four)

-- representative for loop stage carries 4-ray null. use Hess symbol of main, actually secondTerm since turns zero through 2.
lemma lead_true (h:R.Bounds p σ M Λ)(j:ℕ)(hj:j≤2)(m:Side): Tensor.coeff (classicFn p R (f:=m)) j 0=Tensor.coeff (inputSeries p R (m:=m)) j 0 := by
  change Tensor.coeff (intended p R (m:=m)) _ _=_; let F:=inputSeries p R (m:=m)
  let A:= turnSeries R.cubic (m:=m); let B:= turnSeries R.quartic (m:=m)
  have hf:= (stain_knit _ _ h (m:=m)).analytic; have ha:=turns_analytic R.cubic h.width h.three (m:=m); have hb:=turns_analytic R.quartic h.width h.four (m:=m)
  have hu := (rays_jet ha _).1 (turns_low R.cubic h.width h.three (m:=m)); have ht := (rays_jet hb _).1 (turns_low R.quartic h.width h.four (m:=m))
  rw [intent]; unfold Tensor.coeff; rw [iteratedFDeriv_add_apply (hf.add ha).contDiffAt hb.contDiffAt,iteratedFDeriv_add_apply hf.contDiffAt ha.contDiffAt, hu _ (by omega), ht _ (by omega),add_zero,add_zero]
end YM.RG08.Canon
