import YM.Next.UV_STRESS.Dimension
import YM.UVNext.FREE_STRESS_CERTIFICATE.Pivots
import YM.UVNext.FREE_STRESS_CERTIFICATE.StressSpace
import YM.UVNext.FREE_STRESS_CERTIFICATE.VRank



/-!
# Maxwell low-stress certificate

Divergence is on the actual free fields, same normalization. Independent of
unselected stations / interacting weak limit. For E's multiplier `τ` use `torch` (`τ=±1` at ). Fluxes
(`delta` of Lighthouse.Goes with κ=-τ) not asserted here; later consumers
use a `MaxwellData` built with this choice (which entails e.g. proof of those
fluxes).
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Climb Table Work.A01 Next.UVStress Function Set Submodule
variable {G : Gauge} (F : Frames G) (H : (freeTable F).RealSpin) (hG : G.Simple)
variable (W : DiffPlan (freeTable F)) (hW : W.Derivatives (freeTable F)) (ho : W.Orientation H)

def scope := (switch F H 0 1).prod (switch F H 1 2)

include hG hW ho W in
lemma all_samples : Surjective (both F H W ho) := by
  rintro ⟨x,y⟩
  refine ⟨(-x/256) • coilA F H + (-y/512) • coilB F H, ?_⟩
  rw [map_add,map_smul,map_smul,east_column F H hG W hW,west_column F H hG W hW]
  ext <;> simp

include hG hW ho W in
lemma scope_exact : Bijective (scope F H) := by
  let f := scope F H
  have he : Surjective f := by
    intro z; obtain ⟨x,hx⟩ := all_samples F H hG W hW ho z
    exact ⟨currentDiv W H ho x,hx⟩
  refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=f) ?_).mpr he,he⟩
  apply le_antisymm _ (LinearMap.finrank_le_finrank_of_surjective he)
  simpa [Module.finrank_prod] using capped_v F H hG

include hG hW ho W in
theorem rank_on : Surjective (currentDiv W H ho) := by
  intro v
  obtain ⟨x,hx⟩ := all_samples F H hG W hW ho (scope F H v)
  exact ⟨x,(scope_exact F H hG W hW ho).1 hx⟩

def mix : (ℝ × ℝ × ℝ) →ₗ[ℝ] KernelSpace H where
  toFun x := x.1 • coilA F H + x.2.1 • coilB F H + x.2.2 • coilC F H
  map_add' x y := by
    change (x.1+y.1) • _ + (x.2.1+y.2.1) • _ + (x.2.2+y.2.2) • _ = _
    simp only [add_smul]; abel
  map_smul' x y := by simp [mul_smul,smul_add]

include hG hW ho W in
lemma mixed_space : Bijective (mix F H) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨a,b,c⟩ he
    change a • coilA F H+b • coilB F H+c • coilC F H=0 at he
    have h := congr_arg (sightLine F H) he
    have ht := first_pivots F H
    simp only [map_add,map_smul,map_zero,ht.1,ht.2,last_pivot F H hG,smul_eq_mul] at h
    have hc : c=0 := by linarith
    subst c
    have hz := congr_arg (both F H W ho) he
    simp [map_add,map_smul,east_column F H hG W hW,west_column F H hG W hW] at hz
    rw [hz.1,hz.2]; rfl
  intro v; obtain ⟨a,b,c,h⟩ := exhaust F H hG v
  exact ⟨(a,b,c), Subtype.ext h.symm⟩

include hG hW ho W in
lemma line_dim : Module.finrank ℝ (LinearMap.ker (currentDiv W H ho))=1 := by
  have he := LinearMap.finrank_range_add_finrank_ker (currentDiv W H ho)
  rw [LinearMap.range_eq_top.mpr (rank_on F H hG W hW ho),finrank_top] at he
  have h := (LinearEquiv.ofBijective _ (mixed_space F H hG W hW ho)).finrank_eq
  have hp := (LinearEquiv.ofBijective _ (scope_exact F H hG W hW ho)).finrank_eq
  rw [← h,hp] at he; simp only [Module.finrank_prod,Module.finrank_self] at he; omega

-- τ=1 choice (flux factor required would be κ=-1).
def canonicalStress : (freeTable F).Stress := fun a b => panel F a b - if a=b then (1/4:ℂ) • total F else 0

def generator : KernelSpace H := mix F H (1/2,-1/4,1)

theorem lighting : (generator F H).val = canonicalStress F := by
  funext a b
  change ((1/2:ℝ) • _ + (-1/4:ℝ) • _ + (1:ℝ) • across F a b) = _
  dsimp only [coilA, coilB]
  unfold canonicalStress east west across splitDiag
  rcases eq_or_ne a b with rfl|h
  · simp only [if_true,smul_zero,add_zero,total_at F a,near,RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    module
  simp only [if_neg h,smul_zero,one_smul,zero_add,sub_zero]

include hG hW W in
lemma radiating : currentDiv W H ho (generator F H) = 0 := by
  apply (scope_exact F H hG W hW ho).1; rw [map_zero]
  change both F H W ho ((1/2:ℝ) • coilA F H + (-1/4:ℝ) • coilB F H+(1:ℝ) • coilC F H)=0
  simp [east_column F H hG W hW,west_column F H hG W hW,cross_column F H hG W hW]
  norm_num

include hG in
lemma generator_nonzero : generator F H ≠ 0 := by
  intro hh
  have hp := congr_arg (sightLine F H) hh
  change sightLine F H ((1/2:ℝ) • coilA F H + (-1/4:ℝ) • coilB F H + (1:ℝ) • coilC F H)=_ at hp
  rw [map_add,map_add,one_smul,map_smul,map_smul,last_pivot F H hG,(first_pivots F H).1,(first_pivots F H).2,map_zero] at hp
  simp at hp

def torch (τ : ℝ) := τ • canonicalStress F

lemma lit_in (τ : ℝ) : torch F τ ∈ KernelSpace H := by
  unfold torch; rw [← lighting F H]; exact Submodule.smul_mem _ _ (generator F H).property
include hG hW ho in
lemma law (τ : ℝ) : Conserved W H (torch F τ) := by
  unfold torch; rw [← lighting F H]; refine (linear_cons W H ho (τ • generator F H)).1 ?_
  rw [map_smul,radiating F H hG W hW,smul_zero]
include hG H in
theorem lit_ne (τ : ℝ) (he : τ ≠ 0) : torch F τ ≠ 0 := by
  unfold torch; rw [← lighting F H]
  exact smul_ne_zero he (fun hp => generator_nonzero F H hG (Subtype.ext hp))

-- `FreeDiv` is pinned to a Family (as in Dimension).
theorem certificate {C : Family G} (hG : G.Simple) (T : Lighthouse C.book) (H : (Bel C.book).Hierarchy)
    (hW : T.W.Derivatives (Bel C.book)) (ho : T.W.Orientation H.spin)
    (τ : ℝ) (h : τ ≠ 0) (he : T.J=torch C.book.grid τ) : FreeDiv T H ho where
  one := line_dim C.book.grid H.spin hG T.W hW ho
  onto := rank_on C.book.grid H.spin hG T.W hW ho
  enters := he.symm ▸ lit_in C.book.grid H.spin τ
  origin := he.symm ▸ law C.book.grid H.spin hG T.W hW ho τ
  sign := by rw [he]; exact lit_ne C.book.grid H.spin hG τ h

end YM.UVNext.FreeStress
