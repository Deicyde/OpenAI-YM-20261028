import YM.WilsonBulk.Transit.Carrier
import YM.Work.F08.Rows

/-!
# Bridge to BLOCH kernel alphabet

Row/col costs & both period fits. Applicability e.g. center `A_tree`
and curvature projections. First clause in large/small σ uniform proofs.
Doesn't know shape symmetry restrictions needed later. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical ENNReal BigOperators
open Filter Function Pert.Bulk Finset Lattice Laurent Bloch Equiv
open Work.F08
variable {X Y X' Y' U U' : Type} {α β : Type} {L c f : Side} {σ θ p q : ℝ} {n : ℕ}
-- reindex ambient spaces in either position
lemma ferries {P : X→X'} {Q : Y→Y'} {G : Duct X Y} {H : Duct X' Y'} (he : GaugeLine P Q G H)
    (e : U≃ X) (E : U'≃ X') {F : U→ U'} (h : ∀ x,P (e x)=E (F x)) :
    GaugeLine F Q (G ∘ e) (H ∘ E) := by
  constructor
  · intro x y; rw [Function.comp_apply,← h,he.row]; rfl
  intro x y
  let p : {z//F z=x}≃{z//P z=E x}:= Equiv.subtypeEquiv e (fun j=> by rw [h, E.injective.eq_iff])
  rw [Function.comp_apply, he.col, ← p.tsum_eq _]; rfl

def spotCost (L : Side) (σ : ℝ) : Duct (Market α) (Market β) := fun x y=> σ*delta L x.1 y.1
lemma delta_shape (hs : 0 ≤ σ) (h : σ/L.val≤θ) : Geometry (lawn α) (lawn β) θ σ (spotCost L σ) := by
  intro x z y w
  unfold spotCost; apply (mul_le_mul_of_nonneg_left (inv_scaled (L:=L) x.1 y.1 z.1 w.1) hs).trans
  calc _ = σ*delta L x.1 y.1 + σ*delta L z.1 w.1 + (σ/L.val)*sep x.1 z.1 := by ring
       _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right h (sep_nonneg ..)) _ -- maybe add order

def flavor (x : Co c α) : {w:Market α//small c α w=x}≃ {z//wrap c z=x.1} where
  toFun u := ⟨u.val.1,by have h:=congr_arg Prod.fst u.property; exact h⟩
  invFun v:= ⟨(v.val,x.2),Prod.ext v.property rfl⟩
  left_inv p:= by apply Subtype.ext; refine Prod.ext rfl ?_; have h:=congr_arg Prod.snd p.property; exact h.symm
  right_inv _ := Subtype.ext rfl
lemma bidding (u : Market α→ℝ) (x : Co c α) : ∑' z:{w:Market α//small c α w=x},u z.val =∑' z, if wrap c z=x.1 then u (z,x.2) else 0 := by
  rw [← (flavor x).symm.tsum_eq _]; refine Eq.trans (tsum_subtype (s:={z|wrap c z=x.1}) (fun z=>u (z,x.2))) ?_
  exact tsum_congr fun z=> by rw [Set.indicator_apply]; simp only [Set.mem_setOf_eq]

variable [Fintype α] [Fintype β]
lemma plain_gauge (F : Row α β) : GaugeLine (small c α) (small c β) (plain F) (F.acts c) := by
  constructor
  · intro x y; rw [bidding]; exact (matches_plain F x y).symm
  intro x y; rw [bidding (fun v=> plain F v y) x]; have h:= (matches_plain (c:=c) (transRows F) y x).symm; rw [acts_trans] at h
  apply h.trans; unfold display; apply tsum_congr; intro z
  split
  · unfold plain transRows; congr; abel
  exact rfl
lemma plain_audited {F : Row α β} (hσ : 0 ≤ σ) (h : F.strip θ p) (hp : 0 ≤ p) (he : σ ≤ θ) (hh : (n:ℝ)*σ ≤ θ) :
    AuditLine (plain F) (spotCost 1 σ) n ((Fintype.card β)*p) ((Fintype.card α)*p) := by -- need σ≥0
  constructor
  · positivity
  · positivity
  · intro x y; exact mul_nonneg (by assumption) (delta_nonneg ..)
  · intro x; rw [ENNReal.ofReal_mul (by positivity : 0≤(Fintype.card β:ℝ)), ENNReal.ofReal_natCast]; exact convert_market _ _ (fun v=> (plain0 h he).1 x v)
  intro y; rw [ENNReal.ofReal_mul (by positivity : 0≤(Fintype.card α:ℝ)), ENNReal.ofReal_natCast];
  unfold spotCost; simp_rw [← mul_assoc]; apply convert_market; exact fun v=> (plain0 h hh).2 v y

omit [Fintype α] in
def district (L : Side) (α : Type) : Market α ≃ Market (Co L α) where
  toFun x:= (Stationary.rent L x.1,wrap L x.1,x.2)
  invFun x:= (colony L (x.2.1,x.1),x.2.2)
  left_inv x:= by refine Prod.ext ?_ rfl; exact (colony L).apply_symm_apply x.1
  right_inv x:= by
    obtain ⟨hv,h⟩:= (@Stationary.rent_raw L x.1 _ x.2.1 (show colony L (x.2.1,x.1)=_ from rfl)); exact Prod.ext h (Prod.ext hv rfl)

omit [Fintype α] in
lemma towns (g : Ratio c f) (x : Market α) : small c (Co g.count α) (district _ α x)=splitCo g α (small f α x) := by
  rw [split_co]; have h := Stationary.rent_balance g.count x.1
  unfold small
  simp only [g.residue_wrap]; refine Prod.ext ?_ rfl
  rw [show wrap f x.1=g.assemble (wrap c (Stationary.rent g.count x.1),wrap g.count x.1) from by
    rw [Ratio.assemble,Ratio.embed_wrap,← map_add,add_comm,h.symm],g.assemble_parent]; rfl
lemma install_gauge (g : Ratio c f) (H : Cross g.count α β) : GaugeLine (small f α) (small c β) (install H) (installed g H) :=
    ferries (plain_gauge H) (district g.count α) (splitCo g α) (towns g)
omit [Fintype α] [Fintype β] in
lemma install_roll (H : Cross L α β) (x : Market α) (y : Market β) (z : Cover) :
    install H (roll (L.val • z) α x) (roll z β y)=install H x y := by
  let u:= Stationary.rent L x.1; have hz : x.1=lift (wrap L x.1) + L.val • u:= Stationary.rent_balance ..
  obtain ⟨h,hp⟩:= (@Stationary.rent_raw L (u+z) _ (wrap L x.1) (show x.1+ L.val • z= _ by rw [smul_add,← add_assoc,hz.symm]))
  simp only [install,roll_apply,h,hp]; rw [add_sub_add_right_eq_sub]
lemma install_audited {F : Cross L α β} (h : F.strip θ p) (hp : 0≤p) (hs : 0≤σ) (he : σ≤θ) (hh : (n:ℝ)*σ≤θ) :
    AuditLine (install F) (spotCost L σ) n ((Fintype.card β)*(Real.exp (4*σ)*p)) ((Fintype.card α)* ((L.val:ℝ)^4*(Real.exp (4*(n*σ))*p))) := by
  constructor
  · positivity
  · positivity
  · intro x y; exact mul_nonneg hs (delta_nonneg ..)
  · intro y; rw [ENNReal.ofReal_mul (by positivity : 0≤(Fintype.card β:ℝ)), ENNReal.ofReal_natCast]; exact convert_market _ _ (fun i=> cross_row h hs he y i)
  intro y; rw [ENNReal.ofReal_mul (by positivity : 0≤(Fintype.card α:ℝ)), ENNReal.ofReal_natCast];
  unfold spotCost; simp_rw [← mul_assoc (n:ℝ) σ _]; apply convert_market; exact fun i=> cross_col h hp (by positivity) hh i y
end YM.WilsonBulk.Sheet
