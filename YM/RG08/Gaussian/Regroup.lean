import YM.RG08.Gaussian.Repeated
import YM.Pert.Bulk.Crossing

/-! # Strict-transfer regrouping (block-cost, not a contraction) -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Finset Laurent Lattice Wilson RG Precision Exterior Bloch Matrix
open Next.Free Work.F08 Stationary
open scoped Topology BigOperators

variable {α β γ : Type} {L c f : Side}

/-- Delta in old mesh units, relative to actual fixed row. -/
def nativeDelta (L : Side) (r t : Site L) (v : Cover) := Pert.Bulk.colony L (t,v) - lift r
lemma native_arrives (r t : Site L) (x : Cover) : Work.F08.arrives r (nativeDelta L r t x)=t := by
  unfold nativeDelta Work.F08.arrives
  rw [add_sub_cancel]
  exact (rent_raw x _ t rfl).1
lemma native_carry (r t : Site L) (x : Cover) : carry r (nativeDelta L r t x)=x := by
  have he := carry_spec r (nativeDelta L r t x)
  rw [native_arrives,nativeDelta,add_sub_cancel] at he
  exact (rent_raw _ _ t he).2.symm.trans (rent_raw x _ t rfl).2

def nativeRow (L : Side) (H : Row α β) : Row (Co L α) (Co L β) := fun i j z =>
    H i.2 j.2 (nativeDelta L i.1 j.1 z)

lemma native_extent (g : Ratio c f) (i j : Site f) (t : Site g.count) (z : Cover) :
    j=i+wrap f (nativeDelta g.count (g.residue i) t z) ↔
      g.parent j=g.parent i+wrap c z ∧ g.residue j=t := by
  rw [moves_site,native_carry,native_arrives]
  constructor
  · rintro rfl; exact ⟨g.assemble_parent _,g.assemble_res _⟩
  rintro ⟨h,hv⟩; rw [← h, ← hv]; exact (g.unpack_at j).symm

lemma native_price {H : Row α β} {σ η A : ℝ} (hh : H.strip σ A)
    (hp : 0 ≤ η) (he : η ≤ L.val*σ) : (nativeRow L H).strip η (Real.exp (4*η) * A) := by
  intro i j
  let k : Cover → Cover := nativeDelta L i.1 j.1
  have hk : Injective k := fun a b h =>
    (native_carry i.1 j.1 a).symm.trans ((congr_arg (carry i.1) h).trans (native_carry i.1 j.1 b))
  refine Push.AbsoluteSums.budget_mono
      (Push.AbsoluteSums.budget_scale (Real.exp_pos (4*η)).le
        (Push.AbsoluteSums.budget_pull k hk (hh i.2 j.2))) (fun _ => by positivity) ?_
  intro a
  change Real.exp _ * ‖H _ _ _‖ ≤ Real.exp _ * (_ * ‖H _ _ _‖)
  rw [← mul_assoc, ← Real.exp_add]
  have ht := size_scaled (σ:=σ) i.1 (k a) a hp he
  unfold k at *; rw [native_carry, sub_self] at ht
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  rw [add_comm]; simpa using ht

lemma native_whole (L : Side) {H : Row α β} (h : Whole H) : Whole (nativeRow L H) := by
  obtain ⟨σ,C,hp,H⟩ := h
  refine ⟨σ,_,hp,native_price H hp.le (le_mul_of_one_le_left hp.le ?_)⟩
  exact_mod_cast L.property


lemma native_pour (g : Ratio c f) (H : Row α β) (hh : H.safe)
    (x : Site f) (i : α) (y : Site f) (j : β) :
    (nativeRow g.count H).acts c (splitCo g α (x,i)) (splitCo g β (y,j)) = H.acts f (x,i) (y,j) := by
  let r:=g.residue x
  let e : Site g.count × Cover ≃ Cover := (Pert.Bulk.colony g.count).trans (Equiv.addRight (-lift r))
  let v (α : Site g.count × Cover) := if y=x+wrap f (e α) then H i j (e α) else 0
  have he t z : e (t,z)=nativeDelta g.count (g.residue x) t z := by simp only [e,Equiv.trans_apply]; rfl
  let w (a : Cover) := if y=x+wrap f a then H i j a else 0
  have hh' : Summable w := summable_sift (hh i j|>.of_norm) x y
  have Hs : Summable (w ∘ e) := (Equiv.summable_iff e).2 hh'
  have hm : Summable v := Hs
  rw [Row.acts,Matrix.of_apply]
  symm
  calc
    H.acts f (x,i) (y,j) = ∑' u, v u := (e.tsum_eq (fun a : Cover => if y=x+wrap f a then H i j a else 0)).symm
    _ = ∑' t : Site g.count, ∑' z : Cover, v (t,z) := hm.tsum_prod
    _ = _ := by
      rw [tsum_eq_single (g.residue y)]
      · apply tsum_congr; intro z; unfold v; simp [he,native_extent g,split_co,nativeRow]
      intro t ht
      unfold v
      simp_rw [he,native_extent]
      simp [Ne.symm ht]

lemma native_acts (g : Ratio c f) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {H : Row α β} (hv : Whole H) :
    (nativeRow g.count H).acts c=repackM (splitCo g α) (splitCo g β) (H.acts f) := by
  ext i j
  obtain ⟨⟨x,p⟩,rfl⟩ := (splitCo g α).surjective i
  obtain ⟨⟨y,q⟩,rfl⟩ := (splitCo g β).surjective j
  rw [native_pour _ _ hv.safe, repackM,Matrix.submatrix_apply,Equiv.symm_apply_apply,Equiv.symm_apply_apply]

/-- Dye a real stencil with the same color counting convention. -/
def colored (G : Gauge) (H : Row α β) : Row (α × G.ColorIndex) (β × G.ColorIndex) :=
    fun i j z => if i.2=j.2 then H i.1 j.1 z else 0
lemma colored_price (G : Gauge) {H : Row α β} {σ C : ℝ} (h : H.strip σ C) :
    (colored G H).strip σ C := by
  intro i j; by_cases hx : i.2=j.2
  · simpa [Laurent.Width,colored,hx] using h i.1 j.1
  have hv : 0≤C := Push.AbsoluteSums.budget_nonneg (h i.1 j.1)
  simp [Laurent.Width,colored,hx,SumBudget,hv]
lemma colored_whole (G : Gauge) {H : Row α β} (h : Whole H) : Whole (colored G H) := by
  obtain ⟨σ,C,hs,h⟩ := h; exact ⟨_,_,hs,colored_price _ h⟩
lemma colored_acts (G : Gauge) {i j : ℕ} (H : Row (TypeFace i) (TypeFace j)) :
    (colored G H).acts c=FreeResolvent.tensor G (H.acts c) := by
  ext ⟨x,i⟩ ⟨y,j⟩
  rw [FreeResolvent.tensor,Matrix.of_apply]; split_ifs with h
  · change i.2=j.2 at h
    simp [Row.acts,colored,h]
  change _≠_ at h
  simp [Row.acts,colored,show i.2≠j.2 from h]
lemma hessian_rows (G : Gauge) {R T : Row α β} :
    nativeRow L (colored G (minusRows R T))=minusRows
      (nativeRow L (colored G R)) (nativeRow L (colored G T)) := by
  funext i j z; by_cases h : i.2.2=j.2.2 <;> simp [nativeRow,minusRows,colored,h]

end YM.RG08
