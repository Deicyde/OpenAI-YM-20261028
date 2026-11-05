import YM.Contacts.Normal.Rescale
import YM.MultipleContact.Panel.Order

/-! # Local Taylor rule and equations, a single length

Operate on smooth (not necessarily compactly supported) tests in all coordinates. Taylor only the **normal** variables. Tangential derivatives in the test can vary as parameters but are not part of the subtraction jets.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule MultipleContact MultipleContact.Panel
open scoped Topology BigOperators Classical InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Smooth
variable (E)
def SmoothTests : Submodule ℂ (E → ℂ) where
  carrier := { f | ContDiff ℝ ∞ f }
  zero_mem' := (contDiff_const (c:=(0:ℂ)) : ContDiff ℝ ∞ (fun _:E=>(0:ℂ)))
  add_mem' {f g} hf hg := (show ContDiff ℝ ∞ f from hf).add (show ContDiff ℝ ∞ g from hg)
  smul_mem' c f h := (show ContDiff ℝ ∞ f from h).const_smul c
variable {E}
lemma infSmooth (f : SmoothTests E) : ContDiff ℝ ∞ f.val := f.property
lemma lowerSmooth {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : E→Z} (h : ContDiff ℝ ∞ f)(i:ℕ) : ContDiff ℝ (i : ℕ) f:= h.of_le (by exact_mod_cast (show (i:ℕ∞)≤⊤ from le_top))
abbrev Optical (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := SmoothTests E →ₗ[ℂ] SmoothTests E

lemma sum_test {I: Type*} (s : Finset I) (f : I → SmoothTests E) (x : E) : ((∑ i∈s, f i) : SmoothTests E).val x= ∑ i∈s, (f i).val x := by
  induction s using Finset.induction_on with
  | empty=> simp
  | insert a s ha ih=> simp_rw [Finset.sum_insert ha, Submodule.coe_add,Pi.add_apply,ih]

/-- Multiply by a smooth function. -/
def mask (f : SmoothTests E) : Optical E where
  toFun g:= ⟨fun x=> f.val x*g.val x,(infSmooth f).mul (infSmooth g)⟩
  map_add' g h:= Subtype.ext <| funext fun x=> mul_add (f.val x) (g.val x) (h.val x)
  map_smul' c g:= Subtype.ext <| funext fun x=> mul_smul_comm c (f.val x) (g.val x)
end Smooth
end YM.Contacts.Normal
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule MultipleContact MultipleContact.Panel
open scoped Topology BigOperators Classical InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (K : Submodule ℝ E)

def look : Lens E K:= ⟨K.orthogonalProjectionOnto,K.subtypeL,fun y=>orthogonalProjectionOnto_mem_subspace_eq_self y⟩ -- wildcard
lemma looking (x : E) : (look K).put ((look K).read x)=K.starProjection x := rfl
lemma off_at (x : E) : (look K).off x=x-K.starProjection x:=rfl
lemma blind_look (L : Submodule ℝ E) (h : L ≤ Kᗮ) : blind (look K) (look L) := by
  have hu : K ≤ Lᗮ:= (Submodule.le_orthogonal_orthogonal _).trans (Submodule.orthogonal_le h)
  exact ⟨fun y=> Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (h y.property),fun y=> Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (hu y.property)⟩

/-- Term of the *uncut* Taylor polynomial in normal variables. -/
def piece (i : ℕ) : Optical E where
  toFun f:= ⟨(look K).atom i f.val, Lens.atom_smooth _ i (infSmooth f)⟩
  map_add' f g:= by
    apply Subtype.ext; funext x; change (look K).atom i (f.val+g.val) x=_; unfold Lens.atom; rw [iteratedFDeriv_add_apply (lowerSmooth (infSmooth f) i|>.contDiffAt) (lowerSmooth (infSmooth g) i|>.contDiffAt), _root_.add_apply, smul_add]; rfl
  map_smul' c f:= by
    apply Subtype.ext; funext x; change (look K).atom i (c • f.val) x= c • _; unfold Lens.atom; rw [iteratedFDeriv_const_smul_apply (lowerSmooth (infSmooth f) i|>.contDiffAt)]; exact smul_comm ..
lemma piece_formula (i : ℕ) (f : SmoothTests E) (x:E) : (piece K i f).val x =
    (↑i.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ i f.val (x-K.starProjection x) (fun _=>K.starProjection x) := rfl

/-- Radial window **in normal coordinates**, same cutoff profile as for two fields. -/
def window (s : ℝ) : SmoothTests E:= ⟨fun t=> (cutoff s (K.starProjection t):ℂ), Complex.ofRealCLM.contDiff.comp (cutoff_smooth s|>.comp K.starProjection.contDiff)⟩
def jet (m : ℕ) : Optical E:= ∑ i∈Finset.range (m+1), piece K i
/-- `(1−T)` acts on the test only for the projected component, never residue. -/
def taylor (s : ℝ) (m : ℕ) : Optical E:= mask (window K s) ∘ₗ jet K m
def deviation (s : ℝ) (m : ℕ) : Optical E:= LinearMap.id-taylor K s m
lemma jet_formula (m : ℕ) (f : SmoothTests E) (x : E) : (jet K m f).val x=(look K).atoms m f.val x := by
   change (((∑ i∈Finset.range (m+1),piece K i) f) : SmoothTests E).val x = _; rw [LinearMap.sum_apply,sum_test]; rfl
lemma taylor_formula (s : ℝ)(m : ℕ)(f : SmoothTests E)(x : E) : (taylor K s m f).val x=
     cutoff s ((look K).read x) • (look K).atoms m f.val x := by
   change (↑(cutoff s (K.starProjection x)):ℂ)*(jet K m f).val x= _; rw [jet_formula,RCLike.real_smul_eq_coe_mul (K:=ℂ)]; rfl
lemma dev (s : ℝ)(m : ℕ)(f : SmoothTests E)(x : E) : (deviation K s m f).val x=(look K).trim s m f.val x := by change f.val x-(taylor K s m f).val x=_; rw [taylor_formula]; rfl
lemma commute_taylor (L : Submodule ℝ E) (h : L ≤ Kᗮ) (s t : ℝ)(n m:ℕ) : Commute (taylor K s n) (taylor L t m) := by
   have he : Commute (deviation K s n) (deviation L t m):= by
     apply LinearMap.ext; intro x; apply Subtype.ext; change ((deviation K s n) ((deviation L t m) x)).val=((deviation L t m) ((deviation K s n) x)).val
     rw [funext (dev K s n _),funext (dev L t m x),funext (dev L t m _),funext (dev K s n x)]
     exact (blind_look K L h).trim_comm _ _ (infSmooth x) s t
   apply LinearMap.ext; intro f; have h' := LinearMap.congr_fun he.eq f
   change deviation K s n (deviation L t m f)=deviation L t m (deviation K s n f) at h'
   let a:= taylor K s n; let b:=taylor L t m; change f-b f - a (f-b f)= f-a f - b (f-a f) at h'; change a (b f)= b (a f); rw [map_sub,map_sub] at h'; linear_combination (norm := abel) h'

lemma piece_germ {i : ℕ} {x : E} {f g : SmoothTests E} (h : f.val =ᶠ[𝓝 (slide K 0 x)] g.val) : (piece K i f).val =ᶠ[𝓝 x] (piece K i g).val := by
  have ht:= (Continuous.continuousAt (x:=x) (slide K 0).continuous).eventually (h.iteratedFDeriv (𝕜:=ℝ) i)
  filter_upwards [ht] with y hy; simp_rw [slide_zero] at hy; rw [piece_formula,piece_formula,hy]
lemma jet_germ {m : ℕ}{x : E}{f g : SmoothTests E}(h : f.val =ᶠ[𝓝 (slide K 0 x)] g.val) : (jet K m f).val =ᶠ[𝓝 x] (jet K m g).val := by
  filter_upwards [show ∀ᶠ y in 𝓝 x,∀ i∈ Finset.range (m+1),(piece K i f).val y=(piece K i g).val y from (eventually_all_finset _).mpr (fun i hi=> piece_germ K (i:=i) h)] with y hy
  rw [jet_formula,jet_formula]; exact Finset.sum_congr rfl hy
lemma taylor_germ {s : ℝ}{m : ℕ} {x : E}{f g : SmoothTests E}(h : f.val =ᶠ[𝓝 (slide K 0 x)] g.val) : (taylor K s m f).val =ᶠ[𝓝 x] (taylor K s m g).val := by filter_upwards [jet_germ K (m:=m) h] with y hy; exact congr_arg ((window K s).val y*·) hy
lemma taylor_jet_depend (s : ℝ)(m : ℕ) {f : SmoothTests E} (h : ∀ y∈Kᗮ,∀ x∈K, ∀ i ≤ m, iteratedFDeriv ℝ i f.val y (fun _=>x)=0) : taylor K s m f=0 := by
   apply Subtype.ext; funext x; rw [taylor_formula]; suffices he : (look K).atoms m f.val x=0 by rw [he,smul_zero]; rfl
   refine Finset.sum_eq_zero fun i hi=> ?_; change (piece K i f).val x=_; rw [piece_formula,h _ (sub_starProjection_mem_orthogonal x) _ (K.starProjection_apply_mem x) i (by simpa using (Finset.mem_range.mp hi)), smul_zero] -- simp
lemma taylor_off (s : ℝ)(m : ℕ){f : SmoothTests E} (hx : ∀ x∈ Kᗮ, x∉ tsupport f.val): taylor K s m f=0:= by
   apply taylor_jet_depend; intro x hm y hy i hi; rw [notMem_support.mp (show x∉ Function.support (iteratedFDeriv ℝ i f.val) from fun h=> hx _ hm (support_iteratedFDeriv_subset _ h))]; rfl
lemma taylor_support {s : ℝ} (hs : 0 < s) (m : ℕ) (f : SmoothTests E) : tsupport (taylor K s m f).val ⊆
   (slide K 0 ⁻¹' tsupport f.val) ∩ {x | ‖K.starProjection x‖ ≤ 2*s} := by
   apply closure_minimal _ (((isClosed_tsupport _).preimage (slide K 0).continuous).inter (isClosed_le K.starProjection.continuous.norm continuous_const))
   intro x hx; refine ⟨?_,?_⟩
   · by_contra he; have h0:= notMem_tsupport_iff_eventuallyEq.mp (show slide K 0 x∉ tsupport f.val from he)
     have hm:= taylor_germ K (m:=m) (s:=s) (g:=0) h0|>.eq_of_nhds
     rw [map_zero] at hm; exact hx hm
   by_contra! h; have he : 2*s ≤ ‖(look K).read x‖ := le_of_lt (lt_of_not_ge h); exact hx ((taylor_formula K s m f x).trans (by rw [cutoff_eq_zero hs he,zero_smul]))
end YM.Contacts.Normal
