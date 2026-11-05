import YM.Push.LOOP_COEFFICIENT.Paths.Travel

/-!
# Anchored readings of the signed local action, piece by piece
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Function Set Filter Matrix Lattice Laurent RG Bloch Wilson Work.F02 Complex Metric
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {r k : ℕ}

def directSlot (i : PlaqAxes) : Slot := ⟨[],i⟩
def tracePrice (v w : G.Mat) := ((v-1)*(w-1)).trace / (2*G.repDim)
lemma tracePrice_physical (v : G.El) : tracePrice (G.mat v) (G.mat v⁻¹) = (G.price v : ℂ) := by
  have ht (x : ℂ) : star x = (starRingEnd ℂ) x := rfl
  have hr : (G.repDim:ℂ)≠0 := Nat.cast_ne_zero.mpr G.dimPos.ne'
  unfold tracePrice Gauge.price
  rw [sub_mul,mul_sub,← G.mat_mul,mul_inv_cancel,G.mat_one,one_mul,mul_one,trace_sub,trace_sub,trace_sub,trace_one,Fintype.card_fin,G.mat_inv,Matrix.star_eq_conjTranspose,trace_conjTranspose,ht]
  have h := Complex.add_conj (G.mat v).trace
  push_cast at h ⊢; field_simp; linear_combination - h

def directFilm (G : Gauge) (p : Clip) (s : Signed) (i : PlaqAxes) : Film (Angles G) :=
  let w := swung (directSlot i) s
  { radius := 8
    value z := (p.direct:ℂ) * tracePrice (run z 0 w) (run z 0 (Lattice.reverse w))
    inside {x y} h := by
      have he := swung_length (directSlot i) s; change w.length ≤ 2*(0+4) at he
      rw [run_congr (w:=w) (by simpa [size]) h,run_congr (w:=Lattice.reverse _) (by simpa [size,Lattice.reverse]) h] }

lemma directFilm_diff (p : Clip) (s : Signed) (i : PlaqAxes) : ContDiff ℂ ω (directFilm G p s i).reader.value := by
  let w := swung (directSlot i) s
  have h (w) := run_diff (g:=pad (r:=8) (a:=Angles G)) (fun i => contDiff_pi.mpr (pad_contDiff i)) 0 w
  have he := ((h w).sub (g:=fun _ => (1:G.Mat)) contDiff_const).mul ((h (Lattice.reverse w)).sub (g:=fun _ => (1:G.Mat)) contDiff_const)
  let L := (Matrix.traceLinearMap (Fin G.repDim) ℂ ℂ).toContinuousLinearMap
  exact contDiff_const.mul ((L.contDiff.comp (f:=_) he).div_const (2*(G.repDim:ℂ)))
lemma directFilm_merged (p : Clip) (s : Signed) (z : Co n (Angles G) → ℝ) (x : Site n) (i : PlaqAxes) : (directFilm G p s i).value (unwrap z (s.act x)) = p.direct * (G.price (faceValue (pull s 0 (merged z)) (x,i)) : ℝ) := by
  dsimp only [directFilm]; rw [swung, ← turned_reverse,turned_pull,turned_pull,show slotWalk (directSlot i) = square i.val.1 i.val.2 from rfl,
    show travel (pull s 0 (merged z)) x (Lattice.reverse _) = (faceValue _ (x,i))⁻¹ from square_stop x _ _ ▸ travel_reverse _ _ x]; exact congr_arg _ (tracePrice_physical _)

def rowPrice (v w : CColor G) := (v ⬝ᵥ w) / 2

def rowFilm (G : Gauge) (s : Signed) (i j : ℝ × Slot) : Film (Angles G) where
  radius := 2*(i.2.length + j.2.length)
  value z := ((i.1*j.1:ℝ):ℂ) * rowPrice (fieldSlot i.2 s z) (fieldSlot j.2 s z)
  inside h := by rw [fieldSlot_congr (a:=i.2) s (by omega) h,fieldSlot_congr (a:=j.2) s (by omega) h]
lemma rowFilm_diff (s : Signed) (i j : ℝ × Slot) : ContDiff ℂ ω (rowFilm G s i j).reader.value := by
  have he (u) := fieldSlot_diff (g:=pad (r:=(rowFilm G s i j).radius) (a:=Angles G)) (fun i => contDiff_pi.mpr (pad_contDiff i)) u s
  exact contDiff_const.mul ((ContDiff.sum (s:=Finset.univ) (fun k _ => ((contDiff_apply ℂ _ k).comp (he i.2)).mul ((contDiff_apply ℂ _ k).comp (he j.2)))).div_const (2:ℂ))
lemma rowPrice_physical (v w : G.Color) : rowPrice (colorUp G v) (colorUp G w) = ((inner ℝ v w)/2:ℝ) := by rw [rowPrice,color_dot]; push_cast; rfl
lemma rowFilm_merged (s : Signed) (i j : ℝ × Slot) (z : Co n (Angles G) → ℝ) (x : Site n) : (rowFilm G s i j).value (unwrap z (s.act x)) = i.1*j.1*((inner ℝ (i.2.atSite (pull s 0 (merged z)) x) (j.2.atSite (pull s 0 (merged z)) x))/2 : ℝ) := by dsimp only [rowFilm]; rw [fieldSlot_merged,fieldSlot_merged,rowPrice_physical,ofReal_mul]

def atomFilm (s : Signed) (a : Atom G k) : Film (Angles G) where
  radius := 2*a.length
  value z := ∑ b, (a.coeff b : ℂ) * ∏ i,fieldSlot (a.leg i) s z (b i)
  inside h := Finset.sum_congr rfl (fun b _ => congr_arg ((a.coeff b : ℂ)*·) (Finset.prod_congr rfl fun i _ => congr_fun (fieldSlot_congr s (Nat.mul_le_mul_left _ (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => Nat.zero_le ((a.leg i).length)) (Finset.mem_univ i))) h) (b i)))
lemma atomFilm_diff (s : Signed) (a : Atom G k) : ContDiff ℂ ω (atomFilm s a).reader.value := by
  have he i := fieldSlot_diff (g:=pad (r:=(atomFilm s a).radius) (a:=Angles G)) (fun j => contDiff_pi.mpr (pad_contDiff j)) (a.leg i) s
  exact ContDiff.sum fun b _ => contDiff_const.mul (contDiff_prod (f:=fun i z => fieldSlot (a.leg i) s (pad z) (b i)) fun i _ => (contDiff_apply ℂ _ _).comp (he i))
lemma atomFilm_merged (s : Signed) (a : Atom G k) (z : Co n (Angles G) → ℝ) (x : Site n) : (atomFilm s a).value (unwrap z (s.act x)) = a.unmasked (pull s 0 (merged z)) x := by simp only [atomFilm,fieldSlot_merged,colorUp_apply, Atom.unmasked,Atom.poly, ofReal_sum,ofReal_mul,ofReal_prod]
end YM.Push.Loops.Paths
