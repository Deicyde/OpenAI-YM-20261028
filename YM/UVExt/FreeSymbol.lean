import YM.UVExt.FreeTail

/-! Pointwise nondegeneracy of the limiting symbol and convergence on the real momentum torus,
including the harmonic metric (not treating the singular propagator itself as continuous there).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.UV
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG
open scoped Classical Topology BigOperators ComplexConjugate
variable {G : Gauge} (A : Levels G) {k : ℝ} (m : ℕ) {p : Momentum} (a : Axis)

def radial (k : ℝ) (p : Momentum) : ℂ := if h : p ∈ baseCube ∧ p≠0 then
  Classical.choose (cauchySeq_tendsto_of_complete (tail_limitD (A:=A) m a k h.1 h.2)) else 0

lemma tends_D (hp : p∈baseCube) (hn : p≠0) : Tendsto (fun i=>(location A i m).levelD k a p) atTop (𝓝 (radial A m a k p)) := by
  unfold radial; rw [dif_pos (And.intro hp hn)]; exact Classical.choose_spec (cauchySeq_tendsto_of_complete (tail_limitD (A:=A) m a k hp hn))

lemma radial_nonzero (hk : 0 < k) (hp : p∈baseCube) (hn : p≠0) :
    (k:ℝ)⁻¹ ≤ (radial A m a k p).re := by
  have hw := (Complex.continuous_re.tendsto _).comp (tends_D A m a hp hn (k:=k))
  apply ge_of_tendsto hw
  filter_upwards [eventually_gt_atTop m] with i hi
  show (k:ℝ)⁻¹ ≤ ((location A i m).levelD k a p).re
  rw [Train.levelD, loc_land A i m hi]; let T := destination A i m
  have hT := feed_cost T.land a (fun p h => (Silver.chipSq 1 h).inv) p hp.1
  have hb : 1 ≤ (T.land.levelNoise a p).re := by
    change 1 ≤ (feed (.top _) a (fun _=>1) p + Train.stream _ a p).re
    rw [feed_top,Complex.add_re,Complex.one_re,le_add_iff_nonneg_right]
    have he (l) : Silver (Train.stream (j:=A.clock.J m) l a p) := by induction l with
      | nil => exact Silver.zero
      | cons t l ih => exact (feed_cost t a (fun _ _=>Silver.one) p hp.1).add ih
    exact (he _).re_nonneg
  have hh := Silver.real hk.le |>.inv
  have ht : ((↑k)⁻¹ : ℂ).re = k⁻¹ := by simp
  rw [Complex.add_re,hh.real_mul,ht]; exact ((le_mul_of_one_le_right (inv_nonneg.mpr hk.le) hb).trans (le_add_of_nonneg_left hT.re_nonneg))

private def tollInf (k : ℝ) (p : Momentum):ℂ := ∑ a : Axis, jewel 1 p a / radial A m a k p
private lemma tends_rho (hk : 0 < k) (hp : p∈baseCube) (hn : p≠0) :
    Tendsto (fun i=>(location A i m).rho k p) atTop (𝓝 (tollInf A m k p)) := by
  refine tendsto_finsetSum _ fun a _ => tendsto_const_nhds.div (tends_D A m a hp hn) ?_
  exact fun hz => by simpa [hz,hk.not_ge] using radial_nonzero A m a hk hp hn

lemma toll_pos (hk : 0 < k) (hp : p∈baseCube) (hn : p≠0) : 0 < (tollInf A m k p).re := by
  let f (a : Axis) := (radial A m a k p).re
  have hf (a : Axis) : Silver (radial A m a k p) := by
    refine ⟨(radial A m a k p).re, le_trans (inv_nonneg.mpr hk.le) (radial_nonzero A m a hk hp hn),?_⟩
    apply Complex.ext
    · exact (Complex.ofReal_re _).symm
    have him := ((Complex.continuous_im).tendsto _).comp (tends_D A m a hp hn (k:=k))
    rw [Complex.ofReal_im]; apply tendsto_nhds_unique him ((tendsto_const_nhds (x:=(0:ℝ))).congr (fun j=>?_))
    obtain ⟨x,hx,hX⟩ := Train.D_cost k hk (location A j m) a hp.1
    exact (Complex.ofReal_im x).symm.trans (congr_arg Complex.im hX.symm)
  have hPrice t : Silver (jewel 1 p t) := jewel_price 1 _ hp.1
  have hV : ∃ i : Axis, 0 < (jewel 1 p i).re := by
    have h : 0<∑ i : Axis, (jewel 1 p i).re := by
      rw [←Complex.re_sum]; apply lt_of_lt_of_le (b:=meter.low^2*lengthSq p) (mul_pos (pow_pos meter.low_pos _) (lengthSq_pos hn))
      exact (divisor_real_bounds 1 (base_subset_realCube zone_pos hp)).1
    by_contra! hc; exact h.not_ge (Finset.sum_nonpos fun i _=>hc i)
  unfold tollInf; rw [Complex.re_sum]
  simp_rw [fun a=> show (jewel 1 p a / _).re = (jewel 1 p a).re / f a from Silver.real_div (jewel 1 p a) (hf a)]
  exact Finset.sum_pos' (fun a _ => div_nonneg (hPrice a|>.re_nonneg) ((hf a).re_nonneg)) (by
    obtain ⟨a,h⟩ := hV; exact ⟨a,Finset.mem_univ _,div_pos h (lt_of_lt_of_le (inv_pos.mpr hk) (radial_nonzero A m a hk hp hn))⟩)

def pulseLim (k : ℝ) (p : Momentum) := if p=0 then (1:Frequency 2 2) else (tollInf A m k p)⁻¹ • mask 2 (fun i => (radial A m i k p)⁻¹)
lemma pulse_limit (hk : 0 < k) (hp : p∈baseCube) :
    Tendsto (fun i=> pulse k (location A i m) p) atTop (𝓝 (pulseLim A m k p)) := by
  by_cases h : p=0
  · simp only [pulseLim,h,pulse_zero,if_true]; exact tendsto_const_nhds
  unfold pulseLim; simp_rw [if_neg h,pulse_sources _ hk _ (base_subset_realCube zone_pos hp) h]
  have hr := (tends_rho A m hk hp h).inv₀ (fun hz=> by simpa [hz] using toll_pos A m hk hp h)
  apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j
  change Tendsto (fun u=> (Train.rho k (location A u m) p)⁻¹* (mask 2 (fun a=> _ ) i j)) _ (𝓝 ((tollInf A m k p)⁻¹ * (mask 2 (fun a=>_) i j)))
  refine hr.mul ?_
  simp_rw [mask,Matrix.diagonal_apply]
  have H : Decidable (i=j) := Classical.propDecidable _
  by_cases hx : i=j
  · simp only [if_pos hx,inventory]; apply tendsto_finsetProd; intro c _
    exact (tends_D A m c hp h).inv₀ (fun hz=> by simpa [hz,hk.not_ge] using radial_nonzero A m c hk hp h)
  simp only [if_neg hx]; exact tendsto_const_nhds

section finite
variable {k : ℝ} (n : Side)
local notation "M" => Body 2 n
private def bookFrame (n : Side) := rotations n (TypeFace 2)
private def mosaic (sk : Momentum → Frequency 2 2) : Matrix M M ℂ :=
  ((n.val:ℂ)^4)⁻¹ • (bookFrame n * fiber (fun x : Site n => sk (mon x)) * star (bookFrame n))

def stockInf (k : ℝ) := mosaic n (pulseLim A m k) -- k physical penalty

private lemma bookFrame_flip (P : Matrix M M ℂ) : P * bookFrame n * star (bookFrame n) = (n.val:ℂ)^4 • P := by
  rw [Matrix.mul_assoc,bookFrame,rotations_gram,Matrix.mul_smul,Matrix.mul_one]

lemma tends_mosaic (F : ℕ → Momentum → Frequency 2 2) (u : Momentum → Frequency 2 2)
    (he : ∀ p∈baseCube, Tendsto (fun i => F i p) atTop (𝓝 (u p))) : Tendsto (fun i=> mosaic n (F i)) atTop (𝓝 (mosaic n u)) := by
  let f(i : ℕ) : Matrix M M ℂ := fiber fun x : Site n => F i (mon x)
  have H : Tendsto f atTop (𝓝 (fiber fun p:Site n => u (mon p))) := tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => by
    have ht := he (mon i.1) (mon_mem n i.1)
    dsimp only [f,fiber,Matrix.of_apply]; by_cases h : i.1=j.1
    · simpa only [if_pos h] using tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht i.2) j.2
    simpa only [if_neg h] using (tendsto_const_nhds (x:=(0:ℂ)))
  have hmul {f g : ℕ → Matrix M M ℂ} {x y : Matrix M M ℂ}
     (hf : Tendsto f atTop (𝓝 x)) (hg : Tendsto g atTop (𝓝 y)) : Tendsto (fun i=> f i * g i) atTop (𝓝 (x*y)) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j=> tendsto_finsetSum _ fun a _ => ?_
    exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hf i) a).mul (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hg a) j)
  have h := hmul (hmul (tendsto_const_nhds (x:=bookFrame n)) H) (tendsto_const_nhds (x:=star (bookFrame n)))
  exact ((h.const_smul ((n.val:ℂ)^4)⁻¹))

lemma book_identity {j : ℕ} (hk : 0<k) (hv : 4≤j) (v : Train j) : approached ((record (pulse k v)).acts n)=mosaic n (pulse k v) := by
  apply cancel_rotation n
  have hr := (heart_true k hk hv v).1
  
  have hh : ∑ i : Site n, (1:ℂ)=∑ i : Site n, (1:ℂ) := rfl
  have h := circulant n (record (pulse k v)) hr.safe
  simp_rw [hr.echo (mon _) (mon_mem n _)] at h
  calc
    _ = bookFrame n * fiber (fun _ => _) := h
    _ = (((n.val:ℂ)^4)⁻¹ • ((bookFrame n * fiber (fun _ => _))*star (bookFrame n))) * bookFrame n := by
      have hC : star (bookFrame n)*bookFrame n=(n.val:ℂ)^4 • 1 := (rotations_crew n _).2.2
      rw [Matrix.smul_mul, Matrix.mul_assoc (bookFrame n * fiber _),hC,Matrix.mul_smul,smul_smul]
      rw [inv_mul_cancel₀ (pow_ne_zero 4 (Nat.cast_ne_zero.mpr <| Nat.ne_of_gt n.property)), one_smul, Matrix.mul_one]

lemma pulse_period_limit (hk : 0 < k) : Tendsto (fun i=> (record (pulse k (location A i m))).acts n) atTop (𝓝 ((stockInf A m n k).map Complex.re)) := by
  have hx := tends_mosaic n (fun i=>pulse k (location A i m)) (pulseLim A m k) fun p hp => pulse_limit A m hk hp
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hx i) j)
  apply h.congr; intro N; let v:= location A N m; let T:= (record (pulse k v)).acts n; have he := book_identity n hk (A.clock.adm m) v
  exact show (mosaic n (pulse k v) i j).re = T i j from (congr_arg (fun x : Matrix _ _ ℂ => (x i j).re) he.symm).trans (rfl)

end finite
end YM.Next.Free.UV
