import YM.WilsonBulk.Tuning.Spire

/-!
# Use from actual metric ticket: `subdue(full summit) = 1` proof through
  every rank-2 test. Quantities BEFORE any θ-phase or counterterm transport.
  Width derived from ANY positive map price data. Independent of step lengths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open Lattice Laurent Function Filter Bloch Equiv Matrix Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset
open Work.F08 RG FreeResolvent
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {B : Bed} {V : Text (Cloth G) 2} {σ θ p q : ℝ} {Ω : Clip}
open Sheet.Taylor (lineRead league)
-- leading diagonal and symmetry. ticket canonical. Unit at each color.
lemma pair_symm {α : Type} (C : α→α→ℝ) (h : ∀ i j,C i j=C j i) : Regular (pair C) := by intro i; ext1 v; unfold escort pair; cases eq_or_ne (i 0) (0:Fin 2) with
  | inl H=>
     have he : i 1=1:= Fin.eq_of_val_eq (by have he:=i.injective.ne (a₁:=(1:Fin 2)) (a₂:=0) (by decide); rw [H] at he; omega); simp only [Function.comp_apply,H,he]
  | inr H=>
     have hu : i 0=1:= Fin.eq_of_val_eq (by omega)
     have he : i 1=0:= Fin.eq_of_val_eq (by have he:=i.injective.ne (a₁:=(1:Fin 2)) (a₂:=0) (by decide); rw [hu] at he; omega); simp only [Function.comp_apply,hu,he]; exact h ..
lemma resolver_law : resolver.read 0=1 := by
  ext1 i j; rw [masses_tone]; unfold resolver unitRow; simp [Matrix.one_apply,apply_ite ((↑):ℝ→ℂ)]
lemma fund_metric (h : 0 < σ) (hp : B.metric.strip σ p) (h₀ : B.metric.read 0=1) (i j : Axis) (hij : i≠j) :
    (∑' x, actionKernel B.metric (coord j) (coord j) x*stakeLine i x) = -2 := by
  let K:=actionKernel B.metric (coord j) (coord j); have he : Summable fun x=> turf0 (coord j) (coord j) x*stakeLine i x:= finite_pairing one_pos (actionKernel_strip zero_le_one (strip_unit (α:=Two)) _ _) (line_degree i).power
  have hv : HasSum (fun x=> K x*stakeLine i x - turf0 (coord j) (coord j) x*stakeLine i x) 0:= by
    have h':= normalized h hp (strip_unit (α:=Two)) (h₀.trans resolver_law.symm) (coord j) (coord j) _ (line_degree i)
    simpa only [minusRows,sub_mul] using! h'
  have hz:= hv.add he.hasSum; simp only [zero_add,sub_add_cancel, jumpLaw i j hij] at hz; exact hz.tsum_eq
lemma metric_flipping (n : Side) (h : B.metric.strip σ p) (hs : 0 ≤ σ) (ht : (B.metric.acts n).IsSymm) : ((tungsten G B).acts n).IsSymm := by
  rw [tungsten, see_stillColor, match_tensor, actionKernel_acts hs h]; ext ⟨i,j,k⟩ ⟨i',j',k'⟩ -- ext type symm
  have hh:= ksym ht.eq; simp only [Matrix.transpose_apply,tensor,Matrix.of_apply]; split
  next he=> rw [if_pos he.symm, show Precision.K (B.metric.acts n) (i',j') (i,j) =_ from congr_fun (congr_fun hh (i,j)) (i',j')]
  next hn=> rw [if_neg (Ne.symm hn)]
lemma onTop_symm (h : B.metric.strip σ p) (hs : 0 ≤ σ) (he : ∀ n:Side,(B.metric.acts n).IsSymm) : onTop G B=(1/2:ℝ) • pair (plain (tungsten G B)) := by
  let T:=tungsten G B; have hh:= tungsten_cost G (actionKernel_strip hs h)
  have ht : transRows T=T:= Next.Free.bank_injective (Row.rights _ _ (strip_trans hh) hs) (Row.rights _ _ hh hs) (fun n=> by rw [acts_trans]; exact metric_flipping n h hs (he n))
  refine polish_eq (Regular.scaled (pair_symm _ ?_) _); intro i j; unfold plain
  change T _ _ _=T _ _ _; rw [← congr_fun (congr_fun ht i.2) j.2]; unfold transRows; rw [neg_sub] -- ht may not rewrite
lemma born_here (i : G.ColorIndex) (h : 0 < σ) (hq : B.metric.strip σ p) (he : ∀ n:Side,(B.metric.acts n).IsSymm) (h₀ : B.metric.read 0=1) : subdue i (summit G B 0 2)=1 := by
  rw [summit, usher_at, onTop_symm hq h.le he, subdue_pay, subdue,lyric, show (∑' x:Cover, pair (plain (tungsten G B)) (two (0,coord 1,i) (x,coord 1,i))*lineRead (cage x) (noteP 0*noteP 0))=∑' x, actionKernel B.metric (coord 1) (coord 1) x*stakeLine 0 x from ?_, fund_metric h hq h₀ 0 1 (by decide)]; swap
  · apply tsum_congr; intro x; simp only [lineRead,noteP,map_mul,MvPolynomial.eval_X]; change (if i=i then actionKernel _ _ _ (x-0) else 0)*_= _; simp only [sub_zero, ↓reduceIte]; rfl
  norm_num
lemma price_at_horizon {A : Levels G} {X : Horizon A} {F : MapPrices} (h : X.Suffices F) {e n : ℕ} (he : n≤e) (i : G.ColorIndex) : subdue i (summit G (X.H e n) 0 2)=1 := born_here i (F.alpha_pos _) (h.rows _ _ he).2.1 (fun n=> (h.all _ _ he n).symmetric.1) (h.all _ _ he 1).starts
end YM.WilsonBulk.Parapet
