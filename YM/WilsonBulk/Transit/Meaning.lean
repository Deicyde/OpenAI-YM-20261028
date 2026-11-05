import YM.WilsonBulk.Transit.Ferries
import YM.WilsonBulk.Heat.Package

/-!
# Semantics for e-order account under arbitrary sparse pull. Exact finite
polynomial move when stencils all identical (generalize to allowing mixed
directions via Polarization). Proxy control of approximation to mean stencil
on fixed step and period sequence, when its line kernel FIXED. Enough for
using later to validate equations including WT generators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical BigOperators ENNReal
open Function Equiv Filter Pert.Bulk Finset Bloch Lattice Laurent
open MvPolynomial (C X)
variable {X Y : Type} {L : Side} {α β γ : Type} {σ θ δ p q W : ℝ} {k n m : ℕ}
variable {E : Rule X} {F : Rule Y} {T : Legs (Duct X Y) n}
lemma tele_roll {α β : Type} (e : Cover→ Cover) {K : Legs (Duct (Market α) (Market β)) n}
    (h : ∀ i x y b,K i (roll (e b) α x) (roll b β y) = K i x y) {u : Text α n} (hu : Pervasive u) : Pervasive (tele K u) := by
  intro b v; unfold tele; rw [← (casesEquiv (Equiv.refl _) (roll (e b) α)).tsum_eq (fun x=> metal K u (roll b β ∘ v) x)]; apply tsum_congr; intro x; unfold metal lot
  rw [show casesEquiv (Equiv.refl _) _ x= roll (e b) α ∘ x from by rw [casesEquiv_apply]; rfl,hu]; simp only [Function.comp_apply,h]
lemma lot_summable_row (K : Legs (Duct X Y) n) {d : Duct X Y} (h : ∀ i, AuditLine (K i) d n p q) (x : Legs X n) : Summable (lot K x) := by
  have ht := summable_from_receipt (f:=lot K x) (w:=fun y=>∑ i,d (x i) (y i)) (fun y=> sum_nonneg fun i _=> (h i).fronts ..)
  apply ht
  apply ne_top_of_le_ne_top (show (∏ _:Fin n,ENNReal.ofReal p)≠⊤ from by simp)
  simp only [lot,bill_products, all_Δ (a:=fun i y=> bill (K i (x i) y) (d (x i) y))]; exact Finset.prod_le_prod' fun i _=> (h i).row (x i)
lemma lot_summable_col (K : Legs (Duct X Y) n) {d : Duct X Y} (h : ∀ i, AuditLine (K i) d n p q) (y : Legs Y n) : Summable (fun x=>lot K x y) := by
  have ht := summable_from_receipt (f:=fun x=>lot K x y) (w:=fun x=>∑ i,(n:ℝ)*d (x i) (y i)) (fun _=> sum_nonneg fun i _=> mul_nonneg (by positivity) ((h i).fronts ..))
  apply ht; apply ne_top_of_le_ne_top (show (∏ _:Fin n,ENNReal.ofReal q)≠⊤ from by simp)
  simp only [lot,bill_products, all_Δ (a:=fun i x=> bill (K i x (y i)) (n*d x (y i)))]; exact Finset.prod_le_prod' fun i _=> (h i).col (y i)
lemma tele_tends {d : Duct X Y} {T : Legs (Duct X Y) n} (h : ∀ i,AuditLine (T i) d n p q)
    {P : ℕ→ Page X n} {K : Page X n} (hs : 0≤ σ) (hn : n ≠ 0)
    (ht : ∀ᶠ i in atTop, Within E σ W (P i)) (he : Tendsto P atTop (𝓝 K)) : Tendsto (fun i=> tele T (P i)) atTop (𝓝 (tele T K)) := by
  refine tendsto_pi_nhds.mpr fun y=> ?_
  apply tendsto_tsum_of_dominated_convergence ((lot_summable_col _ h y).norm.mul_right W) (fun x=> (tendsto_pi_nhds.mp he x).const_mul (lot T x y))
  refine ht.mono fun i hi x=>?_; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (within_entry hi hs hn x) (norm_nonneg _)
lemma Proxy.tele {K : Text α (n+1)} {c f : ℕ→ Side} (T : Legs (Duct (Market α) (Market β)) (n+1)) (S : ∀ i:ℕ, Legs (Duct (Co (f i) α) (Co (c i) β)) (n+1)) (e : Cover→Cover)
    (hT : ∀ i x y b,T i (roll (e b) α x) (roll b β y)=T i x y) (ht : ∀ᶠ i in atTop,∀ j, GaugeLine (small (f i) α) (small (c i) β) (T j) (S i j))
    {U : Leaf f α (n+1)} (hh : Proxy U K)
    (h : ∀ σ:ℝ,0<σ → ∃ θ : ℝ,0<θ ∧ ∃ k : Duct (Market α) (Market β), Geometry (lawn α) (lawn β) σ θ k ∧ ∃ p q, ∀ i, AuditLine (T i) k (n+1) p q) :
    Proxy (fun i=> tele (S i) (U i)) (tele T K) := by
  obtain ⟨x,A,hx,M,hm,hM⟩:= hh
  obtain ⟨θ,hs,k,g,p,q,h⟩:= h x hx
  refine ⟨θ,q*p^n*A,hs,fun i=>Sheet.tele T (M i), tele_tends h hx.le (by omega) (hM.mono fun i hi=>hi.2.1) hm,?_⟩
  filter_upwards [ht,hM] with i hi hM; exact ⟨tele_roll e hT hM.1, fare_const g h hM.2.1,hM.2.2.tele g h hM.2.1 hs.le hi⟩

-- MVPolynomial substitute semantics
variable [Fintype α] [Fintype β]
def subline (T : Duct α β) (i : α) : Formula β := ∑ j,C (T i j)*MvPolynomial.X j
def voice (T : Duct α β) : Formula α →ₐ[ℝ] Formula β := MvPolynomial.aeval (subline T)
omit [Fintype α] in
lemma voice_joint (T : Duct α β) (x : Legs α n) : voice T (field x) = ∑ y:Legs β n,C (lot (fun (_:Fin n)=> T) x y)*field y := by
  unfold voice field; rw [map_prod]; simp_rw [MvPolynomial.aeval_X,subline]
  simp_rw [lot,map_prod,← prod_mul_distrib]; exact Fintype.prod_sum _
lemma travel_script (T : Duct α β) (P : Page α n) : script (travel T P)=voice T (script P) := by
  simp only [travel,script,tele,tsum_fintype,map_sum,voice_joint,map_mul,sum_mul,mul_sum]
  rw [sum_comm]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_
  rw [show voice T (C (P i))=C (P i) from (voice T).commutes (P i),metal,map_mul]; ring

lemma tele_through [Fintype γ] (T : Legs (Duct α β) n) (S : Legs (Duct β γ) n) (F : Legs (Duct α γ) n)
    (he : ∀ i x y, ∑ j,T i x j*S i j y=F i x y) (u : Page α n) :
    tele S (tele T u)=tele F u := by
  have hv x y : ∑ z : Legs β n, lot S z y*lot T x z= lot F x y := by
    unfold lot; simp_rw [← he]; rw [Fintype.prod_sum]; simp_rw [← prod_mul_distrib]; exact sum_congr rfl fun i _=> prod_congr rfl fun j _=> mul_comm ..
  ext1 y; simp only [tele,metal,tsum_fintype,mul_sum]; rw [sum_comm]; simp_rw [← mul_assoc,← sum_mul,hv]
end YM.WilsonBulk.Sheet
