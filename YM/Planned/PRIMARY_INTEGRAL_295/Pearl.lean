import YM.Planned.PRIMARY_INTEGRAL_295.Twists

/-!
# Unscaled primary transition matrix in archived readings

Uses concrete stencil and `trace` unmodified `A0` transport (later
apply to the earned canonical `Lines` with actual `whole` receipt). The
maps in this calculation are not alternative readouts or demanded paths for
prepaid source histories. They realize, in the same Frame, exact syntax
of the leading term (to be compared). No forcing on remainders / unit
prescribed by a comparison.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Film
open Filter Function Set Lattice Labels RG Wilson Source Source.Drops Precision Bloch Next.Free Place Carrier Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {j m n d t : ℕ} {F : Labels.Frame G d} {M : Side} -- order d before
variable (T : SectionData F) {A : Hol G} {K : Lines M} (h : T.Sound A) (hK : Whole K)
variable (v : F.Coeff)

def seen (K : Lines M) (X : Snap G d) : ℂ := slant T v (trace T.stencil K X)

include h in
lemma still : Parts.Safe (fun X : Snap G d => slant T v (localLane X)) := by
  have ht : ContDiffAt ℝ d (localLane (S:=T.stencil) (G:=G) (d:=d)) 0 := (local_smooth _).of_le le_top
  refine ⟨(((slant_smooth T v).of_le le_top).contDiffAt).comp (0 : Snap G d) ht,fun u=> ?_⟩
  let F := colorIn G d u
  have he : Tendsto F (𝓝 0) (𝓝 0) := by simpa only [map_zero] using F.continuous.tendsto 0
  have hp:=section_comp A T v h
  filter_upwards [he.eventually hp,hp] with i hc hv
  change slant T v (localLane (F i))=slant T v (localLane i)
  exact hc.trans ((congr_arg (T.evaluate v) (color_pure A u i)).trans ((h.gaugeInvariant v ..).trans hv.symm))
include h hK in
lemma seen_safe : Parts.Safe (seen T v K) :=
    ⟨((slant_smooth T v).contDiffAt.comp _ ((trace_smooth hK T.stencil d).contDiffAt)).of_le le_top,
      fun u => Eventually.of_forall fun X : Snap G d => mapped_color T v A h hK u X⟩

/-- Prepayment-free unscaled comparison vector. -/
def bought := Parts.archive (seen_safe T h hK v)

include h in
lemma corner : Parts.archive (still T h v) = F.coords.symm v := by
  classical
  apply Next.Foundations.jet_test_ext
  intro J k hk
  rw [Parts.archive_read (still T h v) hk J]
  have hz := section_comp A T v h
  let S (x : ℝ) := WardBin.engineered x (trunk d J)
  have hp : Tendsto S (𝓝 0) (𝓝 0) := by
    rw [← Parts.engineered_zero (trunk d J)]; exact (WardBin.eng_cont _ 1).continuous.tendsto 0 -- type n
  have he : (fun x : ℝ=> slant T v (localLane (S x))) =ᶠ[𝓝 0] fun x => T.evaluate v (A.links d J x) := by
    filter_upwards [hp.eventually hz] with x hX
    refine hX.trans (congr_arg (T.evaluate v) (scales A J (d:=d) x).symm)
  exact (he.iteratedDeriv_eq k).trans ((h.projects v J).2.2 k hk)

include h hK
lemma bought_unlock (J : Jet G) (hn : n ≤ d) : iteratedDeriv n (fun x => read (scaleJet J x) (bought T h hK v).val) 0 = iteratedDeriv n
    (fun x : ℝ=> seen T v K (WardBin.engineered x (trunk d J))) 0 := Parts.archive_read (seen_safe T h hK v) hn J

private lemma echo_smooth (J : Jet G) : ContDiffAt ℝ d (fun x : ℝ=> seen T v K (WardBin.engineered x (trunk d J))) 0 := by
  let p (x : ℝ) := WardBin.engineered x (trunk d J)
  have hp : p 0=0 := Parts.engineered_zero _
  exact (hp.symm ▸ (seen_safe T h hK v).smooth).comp (f:=p) 0 (WardBin.eng_cont _ _).contDiffAt

omit h hK in
private lemma echo_add (v w : F.Coeff) (X : Snap G d) : seen T (v+w) K X=seen T v K X+seen T w K X := by simp [seen,slant,SectionData.evaluate]
omit h hK in
private lemma echo_smul (a : ℂ) (X : Snap G d) : seen T (a • v) K X=a • seen T v K X := by simp [seen,slant,SectionData.evaluate]

/-- Engineering and slot weights not applied yet. -/
def rawBook : F.Coeff→ₗ[ℂ]Label G d where
  toFun := bought T h hK
  map_add' v w := by
    apply jet_test_ext
    intro J n hn
    let q (v:F.Coeff) := fun x : ℝ=>seen T v K (WardBin.engineered x (trunk d J))
    have he v : ContDiffAt ℝ n (q v) 0 := (echo_smooth T h hK v J).of_le (Nat.cast_le.mpr hn)
    rw [bought_unlock T h hK _ J hn]
    simp_rw [Submodule.coe_add, map_add]
    rw [iteratedDeriv_fun_add (read_smooth J _ _).contDiffAt (read_smooth J _ _).contDiffAt]
    rw [bought_unlock T h hK _ J hn,bought_unlock T h hK _ J hn]; simp_rw [echo_add T (K:=K)] -- args reused?
    exact iteratedDeriv_fun_add (he v) (he w)
  map_smul' z v := by
    apply jet_test_ext; intro J n hn
    simp_rw [Submodule.coe_smul_of_tower,map_smul]
    rw [iteratedDeriv_fun_const_smul (read_smooth J _ _).contDiffAt, bought_unlock T h hK _ J hn,bought_unlock T h hK _ J hn]
    simp_rw [echo_smul T (K:=K)]
    rw [iteratedDeriv_fun_const_smul ((echo_smooth T h hK v J).of_le (Nat.cast_le.mpr hn))]; rfl

def receipt : F.Coeff→ₗ[ℂ] F.Coeff := F.coords.toLinearMap.comp (rawBook T h hK)

lemma stays_zero : rawBook T h hK F.e0 = unit G d := by
  apply jet_test_ext; intro J n hn
  change iteratedDeriv n (fun x => read (scaleJet J x) (bought T h hK F.e0).val) 0 = _
  rw [bought_unlock _ _ _ _ J hn]; simp [seen,slant,h.unit,unit]
lemma pays_unit : receipt T h hK F.e0= F.e0 := by simp [receipt,stays_zero]

omit hK in
private lemma real_spark (X : Snap G d) : seen T (star v) K X=star (seen T v K X) := h.ordinary_real ..
lemma ordinary_real : rawBook T h hK (star v)= realBar (rawBook T h hK v) := by
  apply jet_test_ext; intro J n hn
  change iteratedDeriv n (fun x=> read (scaleJet J x) (bought T h hK (star v)).val) 0 =
    iteratedDeriv n (fun x=> read (scaleJet J x) (conjPol (bought T h hK v).val)) 0
  rw [bought_unlock _ _ _ _ J hn]; simp_rw [conj_value,real_spark T (K:=K) h]
  have ht (f : ℝ → ℂ) : iteratedDeriv n (fun x=>star (f x)) 0=star (iteratedDeriv n f 0) := by
    let K := (starL' ℝ : ℂ ≃L[ℝ] ℂ)
    unfold iteratedDeriv; change iteratedFDeriv ℝ n (K ∘ f) _ _=K _
    rw [K.iteratedFDeriv_comp_left]; rfl
  rw [ht, ht, bought_unlock _ _ _ _ J hn]
lemma pays_conj : receipt T h hK (star v)= star (receipt T h hK v) := by
  rw [receipt,LinearMap.comp_apply,LinearMap.comp_apply,ordinary_real T h hK]
  let X:=bought T h hK v
  change F.coords (realBar X)=star (F.coords X)
  exact funext fun i => by rw [Pi.star_apply,← F.conj_basis,F.coords.symm_apply_apply]

omit hK
variable (s : Signed) (P : Flight j t) (k : ℝ) (hk : 0<k) (ht : 4≤t)
include hk ht
lemma spectral_origin :
    let L:=rawBook T h (stored P k hk ht)
    L (F.act s.ortho v)=tensor s.ortho (L v) := by
  apply jet_test_ext
  intro J n hn
  let hK:=stored P k hk ht
  let g i := Taylor.turn (G:=G) (j:=i) s.ortho⁻¹
  let q := changedJet g J
  change iteratedDeriv n (fun x=> read (scaleJet J x) (bought T h hK (F.act s.ortho v)).val) 0 =
    iteratedDeriv n (fun x=> read (scaleJet J x) (changed g (bought T h hK v).val)) 0
  simp_rw [eval_changed g,show ∀ x, changedJet g (scaleJet J x)=scaleJet q x from fun x=>funext fun i=>map_smul _ _ (J i)]
  rw [bought_unlock _ _ _ _ J hn,bought_unlock _ _ _ _ q hn]
  have he (x : ℝ) : turnIn G d s (WardBin.engineered x (trunk d J))=WardBin.engineered x (trunk d q) := funext fun i=> map_smul (g i.val) _ _
  simp_rw [← he]
  apply congr_arg (fun f=>iteratedDeriv n f 0); exact funext fun x => (swirl T v A h s P k hk ht _).symm
lemma pays_turn :
    let B:=receipt T h (stored P k hk ht)
    B (F.act s.ortho v)=F.act s.ortho (B v) := by
  let hK := stored P k hk ht
  change F.coords (bought T h hK (F.act s.ortho v))=F.act s.ortho (F.coords (bought T h hK v)); rw [Frame.act_coords]
  exact congr_arg F.coords (spectral_origin T h v s P k hk ht)
end YM.Planned.PrimaryIntegral295.Film
