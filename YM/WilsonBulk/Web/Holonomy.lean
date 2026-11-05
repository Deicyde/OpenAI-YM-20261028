import YM.WilsonBulk.Web.Rehearsal

/-!
# Loops, allowed to wind in the proxy but original cover carried separately
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical BigOperators ENNReal
open Function Equiv Lattice Bloch Pert.Bulk Filter
variable {X α : Type} {σ θ p q : ℝ} {k n : ℕ} {c : Side} {u v : Text α n}

def overlay (u : Page X n) (w : Page X k) (φ : Fin k → Fin n) : Page X n :=
    u * (fun v => w (v ∘ φ))
lemma overlay_apply (u : Page X n) (w : Page X k) (φ : Fin k→Fin n) (v : Legs X n) :
    overlay u w φ v=u v*w (v ∘ φ) := rfl
lemma Pervasive.overlaid {w : Text α k} (h : Pervasive u) (hh : Pervasive w) (φ : Fin k→Fin n) :
    Pervasive (overlay u w φ) := h.prod fun b x=> hh b (x ∘ φ)
lemma Within.overlaid {D : Rule X} {u : Page X n} {w : Page X k} (h : Within D σ p u)
    (he : Within D θ q w) (hp : 0≤θ) (hn : k≠0) (φ : Fin k→Fin n) : Within D σ (p*q) (overlay u w φ) :=
    (mul_comm q p) ▸ (h.bound_mul he.1 fun v=> within_entry he hp hn (v ∘ φ))

@[simp] lemma overlay_zero (w : Page X k) (φ : Fin k→ Fin n) : overlay (0:Page X n) w φ = 0 := by unfold overlay; rw [zero_mul]
@[simp] lemma overlay_right_zero (u : Page X n) (φ : Fin k→ Fin n) : overlay u (0:Page X k) φ=0 := by ext; simp [overlay]
lemma overlay_minus {U V : Page X n} {w w' : Page X k} (φ : Fin k→ Fin n) : overlay U w φ - overlay V w' φ = overlay (U-V) w φ + overlay V (w-w') φ := by ext1 v; simp [overlay]; ring
lemma overlay_add (u v : Page X n) (w : Page X k) (φ : Fin k→ Fin n) : overlay (u+v) w φ = overlay u w φ+overlay v w φ := by ext1 p; simp [overlay,add_mul]

lemma oral_sketch {Y : Type} (e : X≃X) (f : Y≃Y) (Λ : X→Y) (H : Semiconj Λ e f) (w : Legs Y n) (x : X) (i : Fin n) :
    ∃ E : Thesis Λ i x w ≃ Thesis Λ i (e x) (f ∘ w), ∀ a : Thesis Λ i x w, (E a).val=e ∘ a.val := by
  have hh : ∀ y:Legs X n, Λ∘ e ∘ y=f ∘ Λ ∘ y := fun y=> funext fun i=>H (y i)
  have hv (y : X) : Λ (e.symm y)=f.symm (Λ y) := f.injective (by rw [← H,Equiv.apply_symm_apply,Equiv.apply_symm_apply])
  refine ⟨{
    toFun a:= ⟨e ∘ a.val, by
      rw [comp_apply,a.property.1,hh,a.property.2]
      trivial⟩
    invFun a:= ⟨e.symm ∘ a.val, by
      rw [comp_apply,a.property.1,symm_apply_apply]
      refine ⟨rfl, funext fun j=>?_⟩; simp only [comp_apply,hv]; rw [show Λ _=_ from congr_fun a.property.2 j]; exact symm_apply_apply ..⟩
    left_inv a:= Subtype.ext (funext fun i=>symm_apply_apply ..)
    right_inv a:= Subtype.ext (funext fun i=>apply_symm_apply ..) }, fun _=> rfl⟩

lemma Orates.switched {Y : Type} {u : Page X n} {v : Page Y n} (e : X≃X) (f : Y≃Y)
    {Λ : X→Y} (H : Semiconj Λ e f) (he : Orates Λ u v) (hh : arabesque e u) (hs : Surjective Λ) (hn : n ≠ 0) : arabesque f v := by
  intro w
  let i : Fin n:=⟨0,by omega⟩
  obtain ⟨x,hx⟩:= hs (w i)
  rw [he i (e x) (f ∘ w) (by rw [H,comp_apply,hx]), he i x w hx.symm]
  obtain ⟨Q,hQ⟩:= oral_sketch e f Λ H w x i; unfold page; rw [← Q.tsum_eq _]
  exact tsum_congr fun a=> by rw [hQ]; exact hh _
lemma printed_roll {U : Page (Co c α) n} (hu : Pervasive u) (he : Orates (small c α) u U) (hn : n ≠ 0) (b : Cover) : arabesque (rolls (wrap c b) α) U :=
  he.switched (roll b α) _ (small_roll c α b) (hu b) (small_onto c α) hn
lemma projected_roll {U : Page (Co c α) n} (hu : Pervasive u) (he : Orates (small c α) u U) (hn : n≠0) : Pervasive (fun v=> U (small c α ∘ v)) := by
  intro b y
  dsimp only; rw [show small c α ∘ (roll b α ∘ y) = (rolls (wrap c b) α) ∘ small c α ∘ y from funext fun i=> small_roll ..]; exact printed_roll hu he hn b _

namespace Proxy
variable {D : ℕ→Side} (hd : Tendsto (fun i=> (D i).val) atTop atTop)
variable {U : Leaf D α n} {V : Leaf D α k} [Fintype α]
-- loop: approximation uses back-pulled periodic metric, NOT equating covariant coefficient
-- growth on winding endpoints. No summability requested for the extended line by itself!
include hd
lemma overlaid {v : Text α k} (hu : Proxy U u) (hv : Proxy V v) (hn : k≠0) (φ : Fin k→Fin n) : Proxy (fun i=> overlay (U i) (V i) φ) (overlay u v φ) := by
  obtain ⟨σ,A,hs,f,H,p⟩:= hu; obtain ⟨θ,B,hθ,g,H',q⟩:= hv
  let w (i : ℕ) : Text α k := fun x=> V i (small (D i) α ∘ x)
  have ht (x : Legs (Market α) k) : Tendsto (fun i=> w i x) atTop (𝓝 (v x)) :=
    printed_limit hd (q.mono fun i hi=>hi.2.1) hθ (q.mono fun i hi=>hi.2.2) H' hn x
  refine ⟨σ,B*A,hs,fun i=> overlay (f i) (w i) φ, tendsto_pi_nhds.mpr (fun x=> (tendsto_pi_nhds.mp H x).mul (ht (x ∘ φ))),?_⟩
  refine (p.and q).mono (fun i ⟨⟨h,hf,h'⟩,⟨t,hg,h''⟩⟩=> ⟨h.overlaid (projected_roll t h'' hn) φ, hf.bound_mul hg.1 (fun x=> printed_bound hg hθ.le h'' hn (small (D i) α ∘ x ∘ φ)), h'.overlay fun _=> rfl⟩)
end Proxy
end YM.WilsonBulk.Sheet
