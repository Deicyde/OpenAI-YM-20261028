import YM.Cells.Packing
import YM.Overlay.Engine
import YM.TimeKernel.Trace
import YM.Vac.Treasury



/-!
# Center cell application

For chosen stop r, one implementation of ALL copies down to r on THE history
and spin-bearing probes. Cost independent of N,p provided input is so. Use
coarser cell level m≤r. Even powers on these probes from Tiling.
No assertion of arbitrary interval tiling phase alignment; origin only for
joint push here. Other translations passed using physical Wilson symmetry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Stock
open Lattice Wilson RG Marker Cells MeasureTheory Filter Set Function Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ENNReal ContDiff

variable {G : Gauge} {C : Family G} {m N p r : ℕ}

def census (V : Type*) [DecidableEq V] [Fintype V] : Census V :=
    { choices := Finset.univ, blank := Finset.mem_univ _, solo := fun _ => Finset.mem_univ _, down := fun _ _ _ => Finset.mem_univ _ }

def final (V : Type*) [DecidableEq V] [Fintype V] : (census V).Mode := ⟨Finset.univ, Finset.mem_univ _⟩

lemma tallies (T : Schedule) (m r p : ℕ) : (Fintype.card (Site (T.side r p)) : ℝ)= (Fintype.card (Site (T.side m p)) : ℝ) * (T.a m/T.a r)^4 := by
  simp only [site_card,Nat.cast_pow]
  rw [← mul_pow]
  congr 1
  field_simp
  rw [eq_div_iff (T.a_pos r).ne',mul_comm (↑(T.side r p).val:ℝ),T.span_side,mul_comm, T.span_side]

lemma spacer (a b c : ℝ) (n : ℕ) (ha : 0≤a) (hb : 0<c) (hn : 0<n) (ht : a*c^n ≤ Real.exp (n*b)) : a^((n:ℝ)⁻¹) ≤ Real.exp b/c := by
  rw [le_div_iff₀ hb]
  have hg : 0 < (n:ℝ) := by exact_mod_cast hn
  refine le_of_pow_le_pow_left₀ (Nat.ne_of_gt hn) (Real.exp_pos _).le ?_
  rw [mul_pow,← Real.rpow_mul_natCast ha,inv_mul_cancel₀ hg.ne',Real.rpow_one,← Real.exp_nat_mul]; exact ht


lemma a_log (S : Schedule) (n : ℕ) : S.a n = Real.exp (-S.scale n) := by
  rw [Schedule.scale,Real.exp_neg,Real.exp_log (inv_pos.2 (S.a_pos _)),inv_inv]

def expPrice (C : Family G) (m r d : ℕ) (W u c d' b : ℝ) :=
    ((C.S.a m/C.S.a r)^4)* YM.Vac.treasury C.path.levels r + u+c+d'*b+
    d*C.S.scale r-Real.log W

lemma est (hN : m≤ N) (h : C.Makes) (F : C.book.Token)
    (L : Lane C.path (census (Site (C.side m p))) N p) (hh : L.Works r) (W u c d' b : ℝ)
    (he : (L.sites r).Radial (fun _ => W) u c d' b) (hW : 0<W) (hq : ∀ i, L.load i=F.1)
    (hx : ∀ i,L.uses i=(center C.S p hN 0).copy i (C.O N p F.2 0)) :
    (center C.S p hN 0).rootTest (C.beta N p) (C.O N p (d:=F.1) F.2 0) ≤ Real.exp (expPrice C m r F.1 W u c d' b) := by
  let T := Site (C.side m p)
  let V := final T
  let n := Fintype.card T
  have h1 : ‖Ride.bump (C.S.a r) V L.load‖=((C.S.a r)^F.1)^n := by
    unfold Ride.bump V final
    simp_rw [hq,norm_prod,norm_pow,Complex.norm_real, Real.norm_of_nonneg (C.S.a_pos r).le,Finset.prod_const,Finset.card_univ]; rfl
  have h2 : Poly.toll (fun _ => W) V=W^n := by simp [Poly.toll,n,V,final]
  let a := C.S.a r
  let X := a^F.1*W
  let b' := ((C.S.a m/C.S.a r)^4)*YM.Vac.treasury C.path.levels r + (u+c+d'*b)
  let M := moment (C.path.β N p N) (Ride.Product L.uses V)
  have H := L.pays h.wilson hh he V
  have H' := H.trans (Real.exp_monotone (YM.Vac.suffices_bill h.wilson hh.admits n ..))
  have e : ‖M‖*X^n ≤ Real.exp ((n:ℝ)*b') := by
    rw [← show C.path.S=C.S from rfl] at h1
    rw [h1] at H'
    have hx₁ : _ ≤ Real.exp (↑(Fintype.card (Site (C.path.levels.clock.schedule.side r p))) * YM.Vac.treasury C.path.levels r +
         ↑n*(u+c+d'*b)) := H'
    change (a^F.1)^n*‖M‖*Poly.toll (R:=(census _)) (fun _ => W) V ≤ _ at hx₁
    rw [show Fintype.card (Site (C.path.levels.clock.schedule.side r p)) = Fintype.card (Site (C.S.side r p)) from rfl, tallies C.S m r p] at hx₁
    change (a^F.1)^n*‖M‖*Poly.toll (R:=(census _)) (fun _ => W) V ≤ Real.exp ((n:ℝ)*_*_ + n*(u+c+d'*b)) at hx₁
    rw [h2,mul_comm _ ‖M‖,mul_assoc, ← mul_pow] at hx₁
    apply hx₁.trans_eq; congr 1; unfold b'; ring



  have hv := C.S.a_pos r
  have hP : (center C.S p hN (0:Site (C.side N p))).rootTest (C.beta N p) (C.O N p (d:=F.1) F.2 0)=‖M‖^(n:ℝ)⁻¹ := by
    unfold M Ride.Product
    simp_rw [hx]; rfl
  apply hP.le.trans
  have hw := spacer _ _ X n (norm_nonneg _) (mul_pos (pow_pos hv _) hW) Fintype.card_pos e
  refine hw.trans_eq ?_
  unfold X a expPrice b'
  rw [a_log C.S r, ← Real.exp_nat_mul, show W=Real.exp (Real.log W) from (Real.exp_log hW).symm] -- rewrite both; handle log
  rw [Real.log_exp,←Real.exp_add, ← Real.exp_sub]; congr 1; ring

lemma rolled (hN : m≤N) (v : C.book.Token) (o i) :
    (center C.S p hN o).copy i (C.O N p v.2 o) = fun U =>
      (center C.S p hN 0).copy i (C.O N p v.2 0) (translate o U) := by
  let X := center C.S p hN o
  let Y := center C.S p hN 0
  have he : X.base=Y.base+o := by ext; simp [X,Y,Cells.center]; abel
  have ht : X.starts i=Y.starts i+o := by
    unfold Tiling.starts; rw [he]; abel
  have ha : X.translateBy i=Y.translateBy i+o-(Y.omega i).act o := by
    unfold Tiling.translateBy
    rw [ht,he]; change Y.starts i+_-(Y.omega i).act _+ Y.bias i=_; rw [Signed.act_add]; abel
  funext U
  have hh : translate o (pull (X.omega i) (X.translateBy i) U)=pull (Y.omega i) (Y.translateBy i) (translate o U) := by
    simp only [←pull_one,pull_pull]
    rw [affine,affine,ha]; change pull ((Y.omega i)*1) _ _ = _; rw [mul_one,one_mul,Signed.act_one]; rw [show X.omega i=Y.omega i from rfl]; congr 1; abel
  have H : C.O N p v.2 o (pull (X.omega i) (X.translateBy i) U)=_ := calc
    _ = C.O N p v.2 0 (translate o (pull (X.omega i) (X.translateBy i) U)) := by rw [C.translation,zero_add]
    _ = C.O N p v.2 0 (pull (Y.omega i) (Y.translateBy i) (translate o U)) := by rw [hh]
  classical
  unfold Tiling.copy; by_cases hx : X.hand i
  · have hy : Y.hand i := hx
    rw [if_pos hx,if_pos hy,H]
  have hy : ¬ Y.hand i := hx; rw [if_neg hx,if_neg hy,H]

lemma translate_s (hn : m≤N) (o) (v : C.book.Token) (hi : Interior ((center C.S p hn 0).chamber 0) (C.O N p v.2 0)) :
    (center C.S p hn o).rootTest (C.beta N p) (C.O N p v.2 o)=(center C.S p hn 0).rootTest (C.beta N p) (C.O N p v.2 0) := by
  let X := Cells.center C.S p hn (0:Site (C.side N p))
  have he := X.manyIntegral (C.beta N p) (fun _ => C.O N p v.2 0) (fun _ => hi)
  have hh := moment_pull (C.beta N p) 1 o _ he
  unfold Tiling.rootTest; apply congr_arg (fun a : ℂ => ‖a‖ ^ ((Fintype.card X.Cell:ℝ)⁻¹))
  simp_rw [rolled hn v o]
  rw [show pull 1 o (K:=G.El)=translate o from funext fun U => pull_one o U] at hh
  exact hh

end YM.Stock
