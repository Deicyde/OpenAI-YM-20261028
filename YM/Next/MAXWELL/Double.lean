import YM.Next.MAXWELL.Mark
import YM.Next.MAXWELL.Stress

/-! # Polarized contraction formula for stress reads -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators

variable {G : Gauge} {j l n : ℕ}

section Body
variable {ι : Type*} (x : Points n) (Q : ι → Factor G) (v : ι → Fin n) (r : List ι)

/-- Offset the bag and park one insertion at y. -/
theorem planted (p : List (Factor G)) {y : E4} (hx : Points.cons y x ∈ conf _) :
    moment G (Points.cons y x) (Fin.cons (α:=fun _ => WickPol G) (p.map letter).prod (bag v Q r)) =
      pairCost linkEntry (p.map (fun i => (y,i)) ++ r.map (beam x v Q)) := by
  let s : Sum (Factor G) ι → Fin (n+1) := Sum.elim (fun _ => 0) (fun i => (v i).succ)
  let t : Sum (Factor G) ι → Factor G := Sum.elim id Q
  let w : List (Sum (Factor G) ι) := p.map Sum.inl ++ r.map Sum.inr
  have hp : Fin.cons (α:=fun _ : Fin (n+1) => WickPol G) (p.map letter).prod (bag v Q r) = bag s t w := by
    ext1 i; refine Fin.cases ?_ (fun i => ?_) i <;>
      simp [s,t,w,bag,List.map_map,Function.comp_def,Ne.symm (Fin.succ_ne_zero _)]
  rw [hp,bag_rec s t w hx]
  unfold w; rw [List.map_append]; congr 2 <;> simp [List.map_map,Function.comp_def,s,t,Points.cons,beam]

lemma front_pair (p q : Factor G) {y : E4} (hx : Points.cons y x ∈ conf _) :
    moment G (Points.cons y x) (Fin.cons (α:=fun _ => WickPol G) (letter p*letter q) (bag v Q r)) =
      pulls r (fun a w => pulls w (fun b s =>
        (linkEntry (beam x v Q a) (y,p)*linkEntry (beam x v Q b) (y,q)) * pairCost (strength x v Q) s)) := by
  have he : (∀ (a : ι) (p : Factor G), linkEntry (y,p) (beam x v Q a) = linkEntry (beam x v Q a) (y,p)) := by
    intro a p; unfold beam
    have hy : y ≠ x (v a) := (show Injective (Points.cons y x).ofLp from hx).ne (Ne.symm (Fin.succ_ne_zero _))
    rw [link_eq _ _ _ _ hy,link_eq _ _ _ _ hy.symm,K_symmetric _ _ hy]
  rw [show letter p * letter q = ([p,q].map letter).prod by simp,planted x Q v r _ hx]
  simp only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,pair_step,pulls_cons,link_zero,zero_mul,zero_add,
    pulls_map,he,pair_transfer]
  unfold pulls
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => (mul_assoc ..).symm
end Body

/-- Linear first label reader, often taking linear combinations *under* the integral. -/
def bookend (x : Points n) (y : E4) (v : Fin n → WickPol G) : WickPol G →ₗ[ℂ] ℂ :=
  (moment G (Points.cons y x)).toLinearMap (Fin.cons (α:=fun _ => WickPol G) 0 v) 0

lemma book_eval (x : Points n) (y : E4) (v : Fin n → WickPol G) (p : WickPol G) :
    bookend x y v p = moment G (Points.cons y x) (Fin.cons (α:=fun _ => WickPol G) p v) := by
  unfold bookend; rw [MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]

section Stress
open scoped InnerProductSpace

def pointing (a : Limb G) := pulse a.2.2 a.1

private def wings (a b : Axis) (y : E4) (p q : Limb G) :=
    ∑ i : Axis, ⟪pointing p a i y,pointing q b i y⟫_ℝ

private def debit (a b : Axis) (y : E4) (p q : Limb G) :=
    wings a b y p q - kr a b*(1/4) * ∑ i : Axis, wings i i y p q

private lemma link_probe (p : Limb G) {y : E4} (hx : p.1 ≠ y) (c : G.ColorIndex) (a b : Axis) :
    linkEntry p (y,⟨0,omegaLeg c a b⟩) = (pointing p a b y c : ℂ) := by
  unfold pointing; rw [show linkEntry p (y,⟨0,omegaLeg c a b⟩) = _ from if_neg hx];
  exact congr_arg ((↑) : ℝ → ℂ) (K_observe p.2.2 c a b hx)

private lemma debit_sym (a b : Axis) (y : E4) (p q : Limb G) : debit a b y p q + debit a b y q p =
    cross (pointing p) (pointing q) a b y := by
  have hw (a b : Axis) : wings a b y q p=wings b a y p q := Finset.sum_congr rfl fun _ _ => real_inner_comm _ _
  unfold debit; simp_rw [hw]; unfold wings cross pointing; rw [Finset.sum_add_distrib]; ring

private theorem power_wings {ι : Type*} (x : Points n) (Q : ι → Factor G) (v : ι → Fin n) (r : List ι)
    {y : E4} (h : Points.cons y x ∈ conf _) (a b : Axis) :
    bookend x y (bag v Q r) (sheetEnergy (G:=G) a b) = pulls r (fun i w => pulls w (fun j s =>
      ((wings a b y (beam x v Q i) (beam x v Q j):ℝ):ℂ)*pairCost (strength x v Q) s)) := by
  have hx (i) : (beam x v Q i).1 ≠ y := (show Injective (Points.cons y x).ofLp from h).ne (Fin.succ_ne_zero _)
  let F := beam x v Q
  let R := pairCost (strength x v Q)
  have he (m : Axis) : bookend x y (bag v Q r) (phi (G:=G) a b m m) =
      pulls r (fun i w => pulls w (fun j s => ((⟪pointing (F i) a m y,pointing (F j) b m y⟫_ℝ : ℝ):ℂ)*R s)) := by
    have hc (c : G.ColorIndex) := front_pair x Q v r ⟨0,omegaLeg c a m⟩ ⟨0,omegaLeg c b m⟩ h
    have hl (c : G.ColorIndex) : bookend x y (bag v Q r) (symbol 0 (omegaLeg c a m)*symbol 0 (omegaLeg c b m)) = _ :=
      (book_eval x y _ _).trans (show _ = _ from hc c)
    unfold phi; simp_rw [map_sum,hl,link_probe (beam x v Q _) (hx _)]
    unfold pulls; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
    have ht (v w : G.Color) : ⟪v,w⟫_ℝ = ∑ i : G.ColorIndex, v i * w i := by rw [real_inner_comm]; rfl
    simp only [← Finset.sum_mul, ht,Complex.ofReal_sum,Complex.ofReal_mul]; rfl
  unfold sheetEnergy; simp_rw [map_sum,he,pulls]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; rw [← Finset.sum_mul];
  dsimp only [wings]; push_cast; rfl

lemma reads_debit {ι : Type*} (x : Points n) (Q : ι → Factor G) (v : ι → Fin n) (r : List ι)
    {y : E4} (h : Points.cons y x ∈ conf _) (a b : Axis) :
    bookend x y (bag v Q r) (polStress G a b) = (1/2) * pulls r (fun i w => pulls w (fun j s =>
      ((cross (pulse (Q i).2 (x (v i))) (pulse (Q j).2 (x (v j))) a b y:ℝ):ℂ) *
      pairCost (strength x v Q) s)) := by
  let Z (i) := beam x v Q i
  let D (i j) := debit a b y (Z i) (Z j)
  let R := pairCost (strength x v Q)
  have hp : (∑ k : Axis, bookend x y (bag v Q r) (sheetEnergy k k)) =
      pulls r (fun i w => pulls w (fun j s => (∑ k : Axis, ((wings k k y (Z i) (Z j):ℝ):ℂ))*R s)) := by
    simp_rw [power_wings x Q v r h,pulls]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_mul]
  let B := pulls r fun i w => pulls w fun j s => ((D i j:ℝ):ℂ) * R s
  have he : bookend x y (bag v Q r) (polStress G a b) = B := by
    unfold polStress; rw [map_sub,map_smul,map_sum,power_wings x Q v r h a b,hp]
    unfold B; unfold pulls D debit
    simp only [smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_sum,Finset.mul_sum,
      Finset.sum_mul,sub_mul,Finset.sum_sub_distrib,mul_assoc,Z,R]
  rw [he]
  let V := fun i j s => (↑(cross (pointing (Z i)) (pointing (Z j)) a b y) : ℂ) * R s
  suffices H : B+B=pulls r (fun i w => pulls w (fun j s => V i j s)) by
    change B=1/2 * pulls r (fun i w => pulls w fun j s => V i j s); rw [H.symm]; ring
  nth_rw 2 [show B=_ from (pulls_twice r (fun i j s => ((D i j:ℝ):ℂ) * R s))]
  unfold B V D pulls; simp_rw [← Finset.sum_add_distrib,← add_mul,← Complex.ofReal_add,debit_sym]
end Stress
end YM.Maxwell.Free
