import YM.WilsonBulk.Web.Rules
import YM.Pert.Bulk.Projected

/-!
# Symmetry under leg permutations and common translations

No signed/reflection/gauge/color identities yet. Covers operations on a
noninvariant root *and* the adapted common-translation relation, to relate to
tagged and finite arrays more easily. Exponential weights always charge *all*
relative displacements. Deterministic Laurent paths can be added only with
reserve.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology BigOperators ENNReal Classical
open Function Equiv Lattice Pert.Bulk Bloch
variable {X Y α β γ : Type} {σ θ p q : ℝ} {k n m : ℕ} {D : Rule X}

variable {u v : Page X n} {w : Legs X n}

def Regular (u : Page X n) := ∀ e : Equiv.Perm (Fin n), escort e u=u
namespace Regular
lemma eq (h : Regular u) (e : Equiv.Perm (Fin n)) (w : Legs X n) : u (w ∘ e)=u w := congr_fun (h e) w
lemma zero : Regular (0:Page X n) := fun _=>rfl
lemma scaled (h : Regular u) (r : ℝ) : Regular (r • u) := fun e=> by rw [escort_scale,h e]
lemma plus (h : Regular u) (g : Regular v) : Regular (u+v) := fun e=> by rw [escort_plus, h e,g e]
lemma minus (h : Regular u) (g : Regular v) : Regular (u-v) := fun e=> by rw [escort_minus, h e,g e]
lemma summed {T : Type} {s : Finset T} {u : T → Page X n} (h : ∀ v∈s,Regular (u v)) : Regular (∑ v∈s,u v) := fun p=> by
  rw [escort_sum]; exact Finset.sum_congr rfl fun i hi=>h i hi p
lemma pay_one {u : Page X n} (h : Regular u) (i : Fin n) (j : Fin n) (x : X) : rent D σ u i x = rent D σ u j x := by
  let e := Equiv.swap i j
  unfold rent; rw [← (casesEquiv e.symm (.refl X)).tsum_eq (fun a=> if a i=x then _ else (0:ℝ≥0∞))]
  apply tsum_congr; intro a
  simp only [casesEquiv_apply, Equiv.symm_symm, Equiv.coe_refl, id_comp,Function.comp_apply,h.eq,run_escort]
  rw [Equiv.swap_apply_left, id_eq]
lemma furnished {u : Text α (n+1)} (h : Regular u) (hh : Folded σ (fun x v => u (hitch x v)) p) (hp : 0≤p) : Within (lawn α) σ p u := by
  refine ⟨hp,fun i x=>?_⟩
  rw [h.pay_one i 0 x, rent_head]; exact hh x
end Regular

abbrev Grouping (n : ℕ) := Equiv.Perm (Fin n)
def polish (u : Page X n) := ((Fintype.card (Grouping n):ℝ))⁻¹ • ∑ e : Grouping n,escort e u
lemma polish_ready (u : Page X n) : Regular (polish u) := by
  intro e
  let v : Grouping n ≃ Grouping n := Equiv.mulLeft e
  unfold polish; rw [escort_scale,escort_sum]; congr 1
  simp_rw [escort_escort]
  exact Equiv.sum_comp v (fun x=> escort x u)
lemma polish_eq (h : Regular u) : polish u = u := by
  unfold Regular at h; unfold polish; simp_rw [h]; ext v; simp [nsmul_eq_mul, show (Fintype.card (Grouping n):ℝ) ≠ 0 by positivity]
lemma Within.clean (h : Within D σ p u) : Within D σ p (polish u) := by
  have he (x : Grouping n) (_ : x∈(Finset.univ : Finset (Grouping n))) := h.reindex x
  have hv := (Within.sum (Finset.univ) he).scale ((Fintype.card (Grouping n):ℝ)⁻¹)
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,abs_of_nonneg (inv_nonneg.mpr (by positivity)),← mul_assoc,inv_mul_cancel₀ (by positivity),one_mul] at hv
  exact hv

@[simp] lemma polish_zero : polish (0:Page X n)=0 := polish_eq Regular.zero
lemma polish_scale (r : ℝ) (u : Page X n) : polish (r • u) = r • polish u := by simp only [polish,escort_scale,← Finset.smul_sum]; rw [smul_comm]
lemma polish_plus (u v : Page X n) : polish (u+v) = polish u + polish v := by simp only [polish,escort_plus, Finset.sum_add_distrib, smul_add]
lemma polish_minus (u v : Page X n) : polish (u-v) = polish u - polish v := by simp only [polish,escort_minus,Finset.sum_sub_distrib, smul_sub]

def arabesque (e : X ≃ X) (u : Page X n) := ∀ v : Legs X n, u (e ∘ v)=u v
variable {a : X ≃ X} {b : Cover} {c : Side}
namespace arabesque
lemma zero : arabesque a (0:Page X n) := fun _ => rfl
lemma plus (h : arabesque a u) (g : arabesque a v) : arabesque a (u+v) := fun w=> by rw [Pi.add_apply,h,g,Pi.add_apply]
lemma minus (h : arabesque a u) (g : arabesque a v) : arabesque a (u-v) := fun w=> by rw [Pi.sub_apply,h,g,Pi.sub_apply]
lemma scale (h : arabesque a u) (r : ℝ) : arabesque a (r • u) := fun w=> by rw [Pi.smul_apply, h,Pi.smul_apply]
lemma prod (h : arabesque a u) (g : arabesque a v) : arabesque a (u*v) := fun w=> by rw [Pi.mul_apply,h,g,Pi.mul_apply]
lemma gather {ι : Type} {s : Finset ι} {u : ι → Page X n} (h : ∀ i∈s, arabesque a (u i)) : arabesque a (∑ i∈s,u i) := by
  intro v; rw [Finset.sum_apply,Finset.sum_apply]; exact Finset.sum_congr rfl fun i hv=> h i hv v
lemma reindex (h : arabesque a u) (e : Fin n≃Fin m) : arabesque a (escort e u) := fun v=> h (v ∘ e)
lemma polished (h : arabesque a u) : arabesque a (polish u) := (gather fun e _=> h.reindex e).scale _
lemma plucked {u : Page X (n+1)} (h : arabesque a u) : arabesque a (pluck u) := by
  intro v; unfold pluck; rw [← a.tsum_eq (fun x=> u (hitch x (a ∘ v)))]; apply tsum_congr; intro x
  rw [← hitch_comp]; exact h _
lemma sewn {u : Page X (n+1)} {v : Page X (k+1)} (h : arabesque a u) (he : arabesque a v) : arabesque a (seam u v) := fun z=> by
  unfold seam
  simp only [crop_comp, snip_comp, keep_comp, Function.comp_apply, ← hitch_comp]
  rw [h,he]
end arabesque

def roll (b : Cover) (α : Type) : Market α≃ Market α := Equiv.prodCongr (Equiv.addRight b) (Equiv.refl _)
def rolls (v : Site c) (α : Type) : Co c α ≃ Co c α := Equiv.prodCongr (Equiv.addRight v) (Equiv.refl _)
lemma roll_zero (α : Type) : roll 0 α = Equiv.refl _ := by ext1 x; rcases x with ⟨x,z⟩; change (x+0,z)=(x,z); rw [add_zero]
lemma roll_add (b c : Cover) (α : Type) : roll (b+c) α=(roll b α).trans (roll c α) := by
  ext1 x; rcases x with ⟨x,z⟩; change (x+(b+c),z)=(x+b+c,z); rw [add_assoc]
lemma roll_undo (b : Cover) (α : Type) : (roll b α).symm=roll (-b) α := by ext1 x; rcases x with ⟨x,z⟩; simp [roll]
lemma roll_apply (b : Cover) (α : Type) (x : Market α) : roll b α x=(x.1+b,x.2) := rfl
lemma rolls_apply (b : Site c) (α : Type) (x : Co c α) : rolls b α x=(x.1+b,x.2) := rfl
lemma lawn_roll (b : Cover) (α : Type) (v x : Market α) : (lawn α).cost (roll b α v) (roll b α x)=(lawn α).cost v x := sep_shift ..
def Pervasive (u : Text α n) := ∀ b : Cover, arabesque (roll b α) u
variable {U V : Text α n}
namespace Pervasive
lemma zero : Pervasive (0 : Text α n) := fun _=> arabesque.zero
lemma plus (h : Pervasive U) (g : Pervasive V) : Pervasive (U+V) := fun b=> (h b).plus (g b)
lemma minus (h : Pervasive U) (g : Pervasive V) : Pervasive (U-V) := fun b=> (h b).minus (g b)
lemma scale (h : Pervasive U) (r : ℝ) : Pervasive (r • U) := fun b=> (h b).scale r
lemma prod (h : Pervasive U) (g : Pervasive V) : Pervasive (U*V) := fun b=> (h b).prod (g b)
lemma gather {ι : Type} {s : Finset ι} {u : ι → Text α n} (h : ∀ i∈s,Pervasive (u i)) : Pervasive (∑ i∈s,u i) := fun b=> arabesque.gather fun i hi=> h i hi b
lemma reindex (h : Pervasive U) (e : Fin n≃ Fin m) : Pervasive (escort e U) := fun b=> (h b).reindex e
lemma polished (h : Pervasive U) : Pervasive (polish U) := (gather fun e _=> h.reindex e).scale _
lemma plucked {u : Text α (n+1)} (h : Pervasive u) : Pervasive (pluck u) := fun b=> (h b).plucked
lemma sewn {u : Text α (n+1)} {v : Text α (k+1)} (h : Pervasive u) (g : Pervasive v) : Pervasive (seam u v) := fun b=> (h b).sewn (g b)
lemma plain_pair (T : Row α α) : Pervasive (Sheet.pair (plain T)) := fun _ _ => plain_reads ..
lemma run_roll (b : Cover) (x : Market α) (u : Legs (Market α) n) : run (lawn α) (roll b α x) (roll b α ∘ u)= run (lawn α) x u := by
  unfold run; exact Finset.sum_congr rfl fun i _=> lawn_roll b α x (u i)
lemma rent_roll (h : Pervasive U) (b : Cover) (x : Market α) (i : Fin n) : rent (lawn α) σ U i (roll b α x)=rent (lawn α) σ U i x := by
  unfold rent; rw [← (casesEquiv (Equiv.refl _) (roll b α)).tsum_eq _]
  apply tsum_congr ; intro v; simp [casesEquiv_apply,run_roll,h b v]
end Pervasive

lemma line_cost {C : Page X 2} : Within D σ p C ↔ 0≤p ∧ (∀ x, ∑'y,bill (C (two x y)) (σ*D.cost x y) ≤ ENNReal.ofReal p) ∧ ∀ x,∑'y,bill (C (two y x)) (σ*D.cost y x) ≤ ENNReal.ofReal p := by
  have hl (x : X) : rent D σ C 0 x = ∑' y, bill (C (two x y)) (σ*D.cost x y) := by
    rw [rent_head,← (identify _).symm.tsum_eq _]; apply tsum_congr ; intro y; simp [two,run,identify]
  have hr (x : X) : rent D σ C 1 x = ∑' y, bill (C (two y x)) (σ*D.cost y x) := by
    change rent D σ C (0 : Fin 1).succ x=_
    rw [rent_tail]; apply tsum_congr; intro y
    rw [← (identify _).symm.tsum_eq (fun v=> if v 0=x then _ else _)]
    simp_rw [show ∀ u:X,(identify X).symm u=(fun _=>u) from fun _=> rfl]
    rw [tsum_eq_single x]; swap; · intro b hb; rw [if_neg hb]
    simp only [↓reduceIte]; rw [← (show two y x = hitch y (fun _=>x) from rfl), run_pair,D.self,add_zero,D.swap x y]
  simp_rw [← hl,← hr]; constructor
  · exact fun h=> ⟨h.1,h.2 0,h.2 1⟩
  intro ⟨h,hh,hi⟩; refine ⟨h,fun i=> ?_⟩
  fin_cases i <;> assumption

lemma lawn_pair {V : Row α α} [Fintype α] (hV : V.strip σ p) (hp : 0 ≤ p) :
    Within (lawn α) σ ((Fintype.card α:ℝ)*p) (pair (plain V)) := by
  -- adapt RowCost and ColCost by batching tail and head positions; no symmetry needed
  apply line_cost.mpr
  rw [ENNReal.ofReal_mul (by positivity : 0≤(Fintype.card α:ℝ)),ENNReal.ofReal_natCast]
  obtain ⟨h,h'⟩:= plain0 hV le_rfl
  refine ⟨by positivity,fun x=> convert_market _ _ (fun v=>?_),fun x=> convert_market _ _ (fun v=>?_)⟩
  · specialize h x v; simp_rw [delta_one] at h; exact h
  specialize h' v x; simp_rw [delta_one] at h'; exact h'
end YM.WilsonBulk.Sheet
