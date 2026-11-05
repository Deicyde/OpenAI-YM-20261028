import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Duplicated
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Press

set_option warningAsError false

/-! All mixed derivatives of the block coefficients on the selected row.
Quantitative after L. Does *not* conclude continuity of a signed sum of
indicator profiles or any Taylor matching estimate on a globally flat field.
Even the Choice and tag orientation on the true S are fixed in this test. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance.Press
open Function Filter Lattice RG RG.Patch Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree
open YM.Push.SectorMeasure YM.Push YM.Next YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f c' f' : Side} {S : StepData c f} {T : StepData c' f'}

-- neighborhood cap on the joint function; more convenient than
-- separating the slots before moving to reference.
def workQ (V : Config G c) (s : Signed) (t : S.Choices) (i : Bond c) (X : Directions G c × Directions G f) :=
  predictGroup (increment V X.1) t s i X.2

def sound (V : Config G c) (s : Signed) (t : S.Choices) (i : Bond c) (X : Directions G c × Directions G f) : G.Color :=
  G.curvature (predictorTurn (increment V X.1) t s i X.2)

lemma sheathed (S : StepData c f) (T : StepData c' f') (s : Signed) (V : Config G c)
    (t : S.Choices) (t' : T.Choices) (rev : Bond f' → Bool) (i : Bond c) (j : Bond c')
    {L : Directions G c →L[ℝ] Directions G f'} {M : Directions G f →L[ℝ] Directions G f'}
    {u v : G.El} {A : Directions G f'} (k : ℕ) {C r : ℝ}
    (h : ∀ B a, pasteQ t' rev j (A,L B,M a)=u*predictGroup (increment V B) t s i a*v⁻¹)
    (hL : ∀ B, ‖L B‖ ≤ ‖B‖) (hM : ∀ a, ‖M a‖ ≤ ‖a‖) (hC : 0≤C) (hr : ‖A‖ ≤ r)
    (he : ∀ x : Trio G f', ‖x‖ ≤ r → ContDiffAt ℝ ω (fun v : Trio G f' => G.mat (pasteQ t' rev j v)) x ∧
        ContDiffAt ℝ ω (rateQ t' rev j) x ∧ AtCap k C (rateQ t' rev j) x) (X : Directions G c × Directions G f)
    (hX : ‖X‖ ≤ r) : ContDiffAt ℝ ω (fun x => G.mat (workQ V s t i x)) X ∧ ContDiffAt ℝ ω (sound V s t i) X ∧
      AtCap k C (sound V s t i) X := by
  let Y := Directions G c × Directions G f
  let p : Trio G f' := (A,0,0)
  let F : Y →L[ℝ] Trio G f' := (show Y →L[ℝ] Directions G f' from 0).prod (L.prodMap M)
  have hv : ‖F‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y; change ‖((0,L y.1,M y.2):Trio G f')‖ ≤ _
    rw [one_mul]; apply max_le
    · rw [norm_zero]; exact norm_nonneg _
    exact max_le_max (hL _) (hM _)
  have hy (x : Y) : p+F x=(A,L x.1,M x.2) := by simp [p,F]; rw [show ((0:Directions G f'),(0:Directions G f'))=0 from rfl,zero_add]; rfl
  obtain ⟨h0,h1,h2⟩ := he (p+F X) (by rw [hy]; exact max_le hr ((max_le_max (hL _) (hM _)).trans hX))
  let R := (G.adjoint u⁻¹).toContinuousLinearMap
  have ht (y : Y) : pasteQ t' rev j (p+F y)=u*workQ V s t i y*v⁻¹ := by rw [hy,h]; rfl
  have hs : sound V s t i=fun y => R (rateQ t' rev j (p+F y)) := by
    funext y
    rw [hy]; unfold rateQ sound
    change _ = G.adjoint u⁻¹ _
    rw [h, ← show M 0=(0:Directions G f') from M.map_zero, h (y.1) 0,← G.curvature_conjugate]
    congr 1; unfold predictorTurn; group
  rw [hs]; refine ⟨?_,R.contDiff.contDiffAt.comp X (slide_smooth F p X h1),AtCap.post R (AtCap.pre F p X h2 hC hv) hC ?_⟩
  · let Q y := G.mat (pasteQ t' rev j (p+F y))
    have hh : ContDiffAt ℝ ω Q X := slide_smooth F p X h0
    have hg (y) : G.mat (workQ V s t i y)=G.mat u⁻¹ * Q y * G.mat v := by
      unfold Q; rw [← G.mat_mul,← G.mat_mul,ht]; group
    simp_rw [hg]; apply (contDiffAt_const.mul hh).mul contDiffAt_const
  apply ContinuousLinearMap.opNorm_le_bound R zero_le_one
  intro z; change ‖G.adjoint _ _‖ ≤ _; rw [G.norm_adjoint,one_mul]

/-- All mixed jets priced even with tag Q's particular endpoint evaluations.
Radius of log-increment variations (and needed flag slack threshold) after L,
period uniform. Holds the fine flags fixed even where the perturbed field is
not valid for those flags. -/
theorem sounds (P : Patch) (K : KernelChoices) (h : P.Branches K G) (k : ℕ) :
    ∃ C r δ : ℝ, 0≤C ∧ 0<r ∧ 0<δ ∧ ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ (x : ℝ) (V : Config G c) (A : Stores S) (F : Forest S.ratio) (s : Signed) (t : S.Choices) (i : Bond c),
      A.flags=RG.flags (temp x) V → span P x ≤ radiusB x/50 → allot P+1 ≤ 9*radiusB x →
      2*(allot P+1)<c.val → permit P * temp x ≤ δ → curb (shots S x) A F x s (.inr i) →
      ∀ X : Directions G c × Directions G f, ‖X‖ ≤ r → ContDiffAt ℝ ω (fun y => G.mat (workQ V s t i y)) X ∧
        ContDiffAt ℝ ω (sound V s t i) X ∧ AtCap k C (sound V s t i) X := by
  obtain ⟨c₀,-,H⟩ := impression P K G h
  let T : StepData c₀ (c₀*P.L) := ⟨P,K,rfl⟩
  obtain ⟨C,r,hC,hr,h0⟩ := plotted T h k
  obtain ⟨E,δ,hE,hδ,h1⟩ := log_chart_cost G
  let d := min δ (r/E)
  refine ⟨C,r,d,hC.le,hr,lt_min hδ (div_pos hr hE),?_⟩
  rintro c f ⟨P₀,K₀,e⟩ hP hK x V A F s t i hA hs hB hc hd he X hX
  change P₀=P at hP; change K₀=K at hK; subst P₀ K₀
  let S : StepData c f := ⟨P,K,e⟩; let o := s.act i.1
  let j : Bond c₀ := (0,i.2)
  obtain ⟨t',q,J,hq,hF⟩ := H e i.1 i.2 (choice (S:=S) s t)
  have hh : o∉A.dome (9*radiusB x + 9*radiusB x/10) := (guarded (S:=S) hs he).1
  obtain ⟨w,hw⟩ := trim (allot P) hh (by omega) hc hA
  have hv u (hu : J u = true) :
      ∃ z : G.Color, ‖z‖ ≤ r ∧ G.lieExp z = gauge w (replica S.ratio V) (sendEdge s 0 (q u)) := by
    let y := gauge w (replica S.ratio V) (sendEdge s 0 (q u))
    have hy : G.chord y ≤ d := by
      apply le_trans _ hd
      refine hw _ ?_
      have he := spin_separation (q u) s i.1 (S:=S); have hz : separation i.1 (S.ratio.parent (q u).1) ≤ predReach P := hq u hu
      change separation o _ ≤ _ at he; change separation o (S.ratio.parent _) ≤ _; unfold allot; omega
    obtain ⟨hg,hN⟩ := h1 y (hy.trans (min_le_left ..))
    refine ⟨_,hN.trans ?_,hg⟩
    rw [mul_comm]; exact (le_div_iff₀ hE).mp (hy.trans (min_le_right ..))
  obtain ⟨A',rev,L,M,u,v,hA',hL,hM,hN⟩ := freshQ S s V w h i t (T:=T) j t' q J hF hr.le hv
  exact sheathed S T s V t t' rev i j k hN hL hM hC.le hA' (h0 t' rev j) X hX
end YM.AnalyticBridge.Covariance.Press
