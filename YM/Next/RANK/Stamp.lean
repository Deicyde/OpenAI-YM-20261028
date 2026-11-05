import YM.Next.RANK.Course
import YM.Next.RANK.Determinant


/-!
# Coefficient from the physical Wilson array

Independent central markers, including conjugation of coefficients on alternating
orientation hands. Exact correction, from the genuine polynomial stamped at N. This
file proves in particular a producer for the root bill from value-order local estimates
on an (unnormalized, complete) pushed density; not assuming Gaussian or replication
costs on the normalized expectation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Array
open Function Set Filter RG Lattice Wilson Cells Marker Glyph Exponential MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff ENNReal

variable {G : Gauge} {n : Side} (T : Tiling n)
variable {V : Type*} [Fintype V] [DecidableEq V] {Y : Config G n → veil V}

open scoped Classical in
def reorient (w : T.Cell) (P : veil V) := if T.hand w then Glyph.shade P else P

lemma turns_prod (w : T.Cell) (P D : veil V) : reorient T w (P*D)=reorient T w P * reorient T w D := by
  classical
  unfold reorient; split <;> simp

lemma turns_pass (w : T.Cell) (P : veil V) : reorient T w (Poly.pass P) = Poly.pass (reorient T w P) := by
  classical
  unfold reorient; split <;> simp [shade_pass]

def tour (Y : Config G n → veil V) (W : T.Cell) (U : Config G n) := reorient T W (Y (Lattice.pull (T.omega W) (T.translateBy W) U))

lemma tour_part (W : T.Cell) (U) (s) : (tour T Y W U).part s=T.copy W (fun U => (Y U).part s) U := by
  classical
  unfold tour reorient Tiling.copy; split <;> rfl

def stamp (β : ℝ) (Y : Config G n → veil V) (U : Config G n) : veil (T.Cell×V) :=
    (bare β U : ℂ) • Glyph.deck (fun i => tour T Y i U)

lemma stamp_part (β : ℝ) (s : modes (T.Cell × V)) U : (stamp T β Y U).part s=
    (bare β U:ℂ) * ∏ i : T.Cell, T.copy i (fun u => (Y u).part (fibre i s)) U := by
  simp only [stamp, Poly.part_smul,deck_part,tour_part]

variable {T}

lemma stamp_vac (h : ∀ U,(Y U).part (quiet V)=1) (U : Config G n) (β : ℝ) (T : Tiling n) :
    (stamp T β Y U).part (quiet _)= bare β U := by
  classical
  have hf (i : T.Cell) : fibre i (quiet _)=quiet V := by rw [← empty_dock (V:=V) i,dock]
  rw [stamp_part]; simp only [hf,h,Tiling.copy]; simp

private lemma copy_cont (f : Config G n → ℂ) (hf : Continuous f) (T : Tiling n) (w : T.Cell) : Continuous (T.copy w f) := by
  classical
  let g (x) := f (Lattice.pull (T.omega w) (T.translateBy w) x)
  have hg : Continuous g := hf.comp (continuous_pull ..)
  change Continuous fun U => T.copy w f U
  by_cases H : T.hand w
  · simpa only [Tiling.copy,H,↓reduceIte,g] using! hg.star
  simpa only [Tiling.copy,H,↓reduceIte] using! hg

lemma stamped_cont (T : Tiling n) (β) (h : ∀ i : modes V,Continuous fun U => (Y U).part i) : Continuous (stamp T β Y) := by
  change Continuous fun U => (stamp T β Y U).part
  apply continuous_pi; intro i
  simp_rw [stamp_part]
  refine Continuous.mul (Complex.continuous_ofReal.comp (bare_cont _)) ?_
  apply continuous_finsetProd _; intro v _; exact copy_cont _ (h _) T _

lemma stamped_all (T : Tiling n) (β : ℝ) (s : modes V) (h : Continuous fun U => (Y U).part s) :
    (∫ U, (stamp T β Y U).part (Glyph.allCells T.Cell s) ∂prior G n)=(Wilson.partition G n β:ℂ)*
      moment β (fun U => ∏ i : T.Cell,T.copy i (fun V => (Y V).part s) U) := by
  rw [moment_formula]
  · simp_rw [stamp_part,Glyph.each,mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (partition_pos _).ne')]
  apply continuous_integrable _ (continuous_finsetProd _ fun i _ => copy_cont _ h T i)

/-- Fixed determinant multiplier on the full array (given the connected polynomial).
Each call to `stamp_mul` applies it even on the subsequent forced-marker summands. -/
def tilt (T : Tiling n) (C : veil V) := ∑ i : T.Cell, insertAt i (reorient T i (-C))



lemma stamp_mul (T : Tiling n) (β : ℝ) (C : veil V) (h : C.part (quiet V)=0) :
    stamp T β (fun u => Poly.pass (-C)*Y u)=fun U => Poly.pass (tilt T C)*stamp T β Y U := by
  classical
  funext U
  simp only [stamp,tour,turns_prod]
  have he : Glyph.deck (fun i => reorient T i (Poly.pass (-C)))=Poly.pass (tilt T C) := by
    simp_rw [turns_pass]; rw [deck_pass]; rfl
    intro i; unfold reorient; split <;> simp [h]
  rw [← he,mul_smul_comm]
  apply congr_arg (fun x : veil (T.Cell × V) => (bare β U:ℂ) • x)
  exact (Glyph.deck_mul (fun i => reorient T i (Poly.pass (-C))) (fun i => tour T Y i U)).symm

section
variable {F : Family G} {N p m k : ℕ} {T : Tiling (F.side N p)}
variable {X : Config G (F.side N p) → veil V} (c : Course F N p k) (hm : m≤N)

lemma flow_vac (T : Tiling (F.side N p)) (h : ∀ i : modes V, Continuous fun U => (X U).part i) (hx : ∀ U,(X U).part (quiet V)=1) :
    (fun U => (c.flow (stamp T (F.beta N p) X) m hm U).part (quiet _))= fun U => (c.vacuum m hm U:ℂ) := by
  let p1 := (Poly.get (R := Stock.census (T.Cell × V)) (quiet _)).restrictScalars ℝ
  let s := stamp T (F.beta N p) X
  have hv : p1 ∘ s = Complex.ofRealCLM ∘ (bare (G := G) (n:=F.side N p) (F.beta N p)) :=
    funext fun i => stamp_vac hx i (F.beta N p) T
  refine (c.flow_linear s p1 ((stamped_cont T _ h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) m hm).trans ?_
  rw [hv,← Course.flow_linear _ _ _ (bare_integrable _) m hm]; rfl

/-- Transport correction exactly back to the stamped Wilson polynomial. -/
lemma flow_corr (T : Tiling (F.side N p)) (h : ∀ i : modes V,Continuous fun U => (X U).part i) (C : veil V)
    (hh : C.part (quiet V)=0) :
    c.flow (stamp T (F.beta N p) fun U => Poly.pass (-C)*X U) m hm =
      fun U => Poly.pass (tilt T C) * c.flow (stamp T (F.beta N p) X) m hm U := by
  let a := Poly.pass (tilt T C)
  let L := (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ a)).restrictScalars ℝ
  rw [stamp_mul _ _ _ hh]
  exact (c.flow_linear _ L ((stamped_cont T (F.beta N p) h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) m hm).symm

lemma flow_credit (T : Tiling (F.side N p)) (s : modes V) (h : ∀ i : modes V,Continuous fun U => (X U).part i) :
    (∫ U,(c.flow (stamp T (F.beta N p) X) m hm U).part (Glyph.allCells T.Cell s) ∂prior G _) =
    (Wilson.partition G (F.side N p) (F.beta N p):ℂ)*moment (F.beta N p) (fun U => ∏ i : T.Cell,T.copy i (fun u => (X u).part s) U) := by
  let b := F.beta N p
  let H := stamp T b X
  let L := Poly.get (Glyph.allCells T.Cell s)
  have hh : Integrable H (prior G _) := (stamped_cont T _ h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ U,L (c.flow H m hm U) ∂_) = _
  rw [L.integral_comp_comm (c.flow_int H hh ..), Course.flow_sum _ _ hh, ← L.integral_comp_comm hh]; exact stamped_all T b s (h s)

-- root from the terminal notice and *matched denominator*. Read the leftover wrap prices.

theorem postage (o : HaarBudget G) {P : Rep G (F.side m p)} (hp : c.Uses m hm P)
    {σ A Λ δ ν g : ℝ} (hP : P.Lawful σ A Λ δ ν)
    (hg : 0<g) (he : g≤P.p.threshold) (hβ : P.beta*g^2=1)
    (tz : Fintype.card T.Cell = Fintype.card (Site (F.side m p)))
    {r e l L : ℝ} (hr : 0<r) (eu : 0 ≤ e)
    (h : ∀ i : modes V,Continuous fun U => (X U).part i)
    {ζ : T.Cell×V → Site (F.side m p)}
    (H : Value.Notice P ζ (c.flow (stamp T (F.beta N p) X) m hm) (fun _ => r) e l L) (s : modes V) :
    T.rootTest (F.beta N p) (fun U => (X U).part s) ≤
      Real.exp (protection o P A Λ δ (L+(Fintype.card V:ℝ)*l) g-4*G.lieDim*Real.log g / (Fintype.card T.Cell:ℝ)) / r^s.val.card := by
  let q := Fintype.card T.Cell
  have hq : 0<q := T.cells_positive
  let b := F.beta N p
  let S := Glyph.allCells T.Cell s
  let Y := c.flow (stamp T b X) m hm
  have hi := hP
  have hu : (∫ U,P.eval U∂prior G _) = Wilson.partition G (F.side N p) b := hp.density ▸ c.vacuum_total hm
  have hpos : ∀ U,0 ≤ P.eval U := hp.density ▸ c.vacuum_lower hm
  have ht : 1 < (F.side m p).val := by
    exact lt_of_lt_of_le (by norm_num : 1 < 4) (Nat.le_of_dvd (F.side m p).property (F.S.side_four m p))
  have hd := determinant hi o hpos ht hg he hβ (fun U => (Y U).part S) (by
    exact (Poly.get S).integrable_comp (c.flow_int _ ((stamped_cont T b h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ..))
    (show 0 ≤ Poly.toll (fun _ => r) S from (Poly.worth (fun _ => hr) _).le) (X:=L+(Fintype.card V:ℝ)*l) (fun U => by
      refine (Poly.member (fun _ => hr) _ _).trans ((H.price (fun _ => hr) eu U).trans_eq ?_);congr 1
      rw [Fintype.card_prod, tz]; push_cast; ring)
  let C := protection o P A Λ δ (L+(Fintype.card V:ℝ)*l) g
  let pN := Wilson.partition G (F.side N p) b
  have ha : 0<pN := partition_pos _
  have H' : (r^s.val.card)^q * ‖moment b (fun U => ∏ i : T.Cell,T.copy i (fun u => (X u).part s) U)‖ ≤ Real.exp (q*C-4*G.lieDim*Real.log g) := by
    dsimp only [Y] at hd
    rw [flow_credit _ _ T s h, hu,norm_mul,Complex.norm_real,Real.norm_of_nonneg ha.le,← tz,Glyph.all_price s r] at hd
    apply le_trans _ hd; apply le_of_eq; symm; apply (div_eq_iff ha.ne').2; dsimp only [pN,q,b]; ring
  apply Stock.spacer _ _ _ q (norm_nonneg _) (pow_pos hr s.val.card) hq
  rw [mul_comm]; apply H'.trans_eq; congr 1; dsimp only [C]
  have hx : 0 < (q:ℝ) := by exact_mod_cast hq
  change (q:ℝ)*_ -_=_*(_-_/q)
  field_simp
end
end YM.Next.Rank.Array
