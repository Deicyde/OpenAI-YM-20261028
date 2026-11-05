import YM.Extra.SOURCE_HISTORIES.Pencil

/-! Signed axes and ordinary-conjugation rebasing at the central block.

`act` isn't treated as preserving the l1 norm. The finite cost is at this
label-frame stage, and it DOES preserve the relevant grades/weights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ}

abbrev Motion := Signed × Bool

namespace Motion
variable (F : Labels.Frame G d)

def nil : Motion := (1,false)
def backward (m : Motion) : Motion := (m.1⁻¹,m.2)

def scalar (m : Motion) (c : ℂ) := if m.2 then star c else c

def patch (m : Motion) (v : F.Coeff) := if m.2 then star (F.act m.1.ortho v) else F.act m.1.ortho v

lemma patch_id (v : F.Coeff) : patch F nil v = v := by
  unfold patch nil
  rw [show (1 : Signed).ortho=1 from map_one Signed.inclusionO]; simp
lemma act_conj (v : F.Coeff) (s : Ortho) : F.act s (star v)=star (F.act s v) := by
  have hq (x : F.Coeff) : F.coords (realBar (F.coords.symm x)) = star x :=
    funext fun _ => F.conj_basis ..
  rw [← hq,← hq]; simp [Frame.act]
lemma scalar_add (m : Motion) (a b : ℂ) : scalar m (a+b) = scalar m a+scalar m b := by
  unfold scalar; split <;> simp
lemma scalar_mul (m : Motion) (a b : ℂ) : scalar m (a*b) = scalar m a*scalar m b := by
  unfold scalar; split <;> simp
lemma scalar_self (m : Motion) (a : ℂ) : scalar m (scalar m a)=a := by unfold scalar; split <;> simp
lemma scalar_real (m : Motion) (a : ℝ) : scalar m (a:ℂ)=a := by unfold scalar; split <;> simp
lemma norm_scalar (m : Motion) (a : ℂ) : ‖scalar m a‖=‖a‖ := by unfold scalar; split <;> simp
lemma patch_add (m : Motion) (x y : F.Coeff) : patch F m (x+y) = patch F m x+patch F m y := by
  unfold patch; split <;> simp
lemma patch_smul (m : Motion) (c : ℂ) (x : F.Coeff) : patch F m (c•x) = scalar m c • patch F m x := by
  unfold patch scalar; split <;> simp
lemma round (m : Motion) (v : F.Coeff) : patch F m (patch F (backward m) v)=v := by
  unfold patch backward
  simp only [show (m.1⁻¹).ortho = m.1.ortho⁻¹ from map_inv Signed.inclusionO _]
  split <;> rename_i h
  · simp [act_conj,← Frame.act_mul]
  simp [← Frame.act_mul]
lemma patch_inj (m : Motion) : Injective (patch F m) := by
  have he : backward (backward m)=m := by simp [backward]
  intro i j h
  have hq := congr_arg (patch F (backward m)) h
  have hb (x) := round F (backward m) x
  rw [he] at hb
  rwa [hb,hb] at hq
lemma patch_sum {ι : Type*} [Fintype ι] (m : Motion) (v : ι → F.Coeff) :
    patch F m (∑ i, v i)=∑ i, patch F m (v i) := by
  unfold patch
  split <;> simp_all only [map_sum,star_sum]
lemma patch_series {ι : Type*} (m : Motion) {v : ι → F.Coeff} {x} (hv : HasSum v x) :
    HasSum (fun i => patch F m (v i)) (patch F m x) := by
  have hr := (F.act m.1.ortho).toContinuousLinearMap.hasSum hv
  cases m with | mk s q => cases q; exact hr; exact hr.star

lemma act_diag (c : ℕ × ℕ → ℂ) (s : Ortho) (v : F.Coeff) :
    F.act s (fun i => c (F.grades i)*v i) = fun i => c (F.grades i)*F.act s v i := by
  let T : F.Coeff →ₗ[ℂ] F.Coeff := {
    toFun v i := c (F.grades i)*v i
    map_add' x y := by ext; simp [mul_add]
    map_smul' x y := by ext; simp; ring }
  have hb (x : Label G d) (m) (hx : x∈Grade m) : T (F.coords x)=c m • (F.coords x) := by
    funext i
    by_cases he : m=F.grades i
    · rw [he]; rfl
    change _ * _ = c m * _; simp [F.power_coefficient i he hx]
  have h : ((F.act s).comp T).comp F.coords.toLinearMap = (T.comp (F.act s)).comp F.coords.toLinearMap := by
    apply F.basis.ext
    intro i
    let b := F.basis i
    have hs : tensor s b ∈ Grade (F.grades i) := by
      have he := gradePart_mem (F.grades i) (tensor s b)
      rw [gradePart_turn,gradePart_self b _ (F.pure i)] at he; exact he
    change F.act s (T (F.coords b))=T (F.act s (F.coords b))
    rw [hb b _ (F.pure i),map_smul,F.act_coords,hb _ _ hs]
  obtain ⟨x,rfl⟩ := F.coords.surjective v
  exact LinearMap.congr_fun h x

lemma core_patch (m : Motion) (v : F.Coeff) : patch F m (F.core v)=F.core (patch F m v) := by
  have he (v : F.Coeff) : F.core v = fun i => (if (F.grades i).2=0 then (0:ℂ) else 1)*v i := by
    ext i
    change update .. = _
    by_cases hi : i=0
    · subst i; simp [F.zero_degree]
    simp [update_of_ne hi, (F.factors_pos i hi).ne']
  simp only [he]
  have ht := act_diag F (fun i => if i.2=0 then 0 else 1) m.1.ortho v
  unfold patch
  split <;> rename_i h
  · rw [ht]; funext i; split_ifs <;> simp [*]
  exact ht

lemma patch_vowel (m : Motion) (L : Side) (v : F.Coeff) :
    patch F m (vowel F L v)=vowel F L (patch F m v) := by
  unfold patch vowel
  have he := act_diag F (fun i => (L.val:ℂ)^(d-i.1)) m.1.ortho v
  split <;> rename_i h
  · rw [he]; funext i; simp
  exact he

lemma patch_unit (m : Motion) : patch F m F.e0=F.e0 := by
  have he : F.act m.1.ortho F.e0 = F.e0 := by
    rw [← F.coords_unit,F.act_coords]; apply congr_arg; exact Subtype.ext ((rotated _).map_one)
  unfold patch; split <;> rename_i h
  · rw [he]; ext i; by_cases hi : i=0 <;> simp [Frame.e0, hi]
  exact he

/-- Fixed d, finite price before any L. Use for PAPER at the same frame F. -/
def orbitCost := 1 + ∑ m : Motion, ∑ i, F.coeffSize (patch F m (Size.axis F i))
lemma orbitCost_one_le : 1 ≤ orbitCost F :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Work.G08.size_nonneg F _)

set_option maxRecDepth 4000 in
lemma patch_cost (m : Motion) (v : F.Coeff) : F.coeffSize (patch F m v) ≤ orbitCost F * F.coeffSize v := by
  have hz (i) : F.coeffSize (patch F m (Size.axis F i)) ≤ orbitCost F := by
    let f (m : Motion) (i) := F.coeffSize (patch F m (Size.axis F i))
    have ht (j : Motion) (i) : 0 ≤ f j i := Work.G08.size_nonneg F _
    have hi : f m i ≤ ∑ j, f m j := Finset.single_le_sum (fun j _ => ht m j) (Finset.mem_univ _)
    have he : ∑ j, f m j ≤ ∑ s : Motion, ∑ j, f s j := Finset.single_le_sum (fun j _ =>
      Finset.sum_nonneg fun i _ => ht j i) (Finset.mem_univ m)
    exact hi.trans (he.trans (le_add_of_nonneg_left zero_le_one))
  nth_rw 1 [← Size.sum_axes F v]
  rw [patch_sum]
  refine le_trans (Size.finite F _ _) ?_
  simp_rw [patch_smul,Size.smul,norm_scalar]
  rw [Frame.coeffSize,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => by rw [mul_comm (orbitCost F)]; exact mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _))

section transfer
variable {n : Side}

def dance (m : Motion) (F : Config G n → ℂ) (U : Config G n) := scalar m (F (pull m.1 0 U))
lemma dance_nil (f : Config G n → ℂ) : dance nil f=f := by
  ext1 U
  have he : translate 0 U = U := funext fun i => by simp [translate]
  simp [dance,nil,scalar,pull_one,he]

lemma scalar_tsum {ι : Type*} (m : Motion) (f : ι → ℂ) : scalar m (∑' i, f i)=∑' i,scalar m (f i) := by
  unfold scalar; split <;> simp_all only [tsum_star]

lemma push_pull (H : History G) (i p : ℕ) (β : ℝ) (s : Signed) (b : Site (H.S.side i p))
    (f : Config G (H.S.side (i+1) p) → ℂ) (hi : Integrable f (prior G _)) (V) :
    let S := H.levels.clock.op i p
    S.push β (fun U => f (pull s (S.ratio.embed b) U)) V = S.push β f (pull s b V) := by
  intro S
  let k := pull s (S.ratio.embed b) (K:=G.El)
  let m : Measure (Config G (H.S.side (i+1) p)) := prior G _
  have he : MeasurePreserving k m m := prior_pull ..
  let A (U) := S.density β U (pull s b V) • f U
  have hx : ∫ U,A U ∂m = ∫ U, A (k U) ∂m := by
    have hh : AEStronglyMeasurable A (Measure.map k m) := by
      rw [he.map_eq]; exact (StepData.push_slice (H.levels.transition_mass ..) _ _ hi).aestronglyMeasurable
    rw [← integral_map he.aemeasurable hh, he.map_eq]
  change (∫ U, S.density β U V • f (k U) ∂m) = ∫ U,A U ∂m
  have hy U : S.density β U V = S.density β (k U) (pull s b V) := ((H.levels.blocks i p).symmetric β U V s b).symm
  rw [hx]
  apply integral_congr_ae
  exact .of_forall (fun U => congr_arg (· • f (k U)) (hy U))

lemma embed_origin {d' : Side} (g : Ratio n d') : g.embed 0=0 := by
  unfold Ratio.embed
  rw [show lift (0:Site n)=0 by ext; simp [lift]]; simp

/-- Algebraic compatibility for the shared tag convention. -/
lemma push_dance (H : History G) (i p : ℕ) (β : ℝ) (m : Motion)
    (f : Config G (H.S.side (i+1) p) → ℂ) (hi : Integrable f (prior G _)) :
    let S := H.levels.clock.op i p
    S.push β (dance m f) = dance m (S.push β f) := by
  intro S
  funext V
  have he := push_pull H i p β m.1 0 f hi V
  dsimp only at he
  rw [embed_origin] at he
  cases m with
  | mk s z =>
    cases z
    · exact he
    change S.push β (fun U => star (f (pull s 0 U))) V = star (S.push β f (pull s 0 V))
    dsimp only at he; rw [show S.push β f (pull s 0 V) = _ from he.symm]
    unfold StepData.push
    let L := starL' ℝ (A:=ℂ)
    simp_rw [← show ∀ (r : ℝ) (z : ℂ), star (r • z) = r • star z from fun r z => by rw [star_smul,star_trivial]]
    exact L.integral_comp_comm _
end transfer
end Motion
end YM.Extra.Histories
