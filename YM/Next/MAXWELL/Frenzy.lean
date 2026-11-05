import YM.Next.MAXWELL.Morsels
import YM.Next.MAXWELL.Silt


/-!
# Multilinear collision calculus
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} {j k l n r M : ℕ}

abbrev ActMap (n : ℕ) (G : Gauge) := MultilinearMap ℂ (fun _ : Fin n => WickPol G) ℂ
abbrev charge (p : Probe G k) (s : ℕ) (i : Fin (legDim G s)) : Scatter := fun z => (legKernel p (coordinateLeg (keyAt s i)) z : ℂ)

def wield (Q : ActMap n G) (j : Fin n) (B : Module.End ℂ (WickPol G)) : ActMap n G := Q.compLinearMap fun i => if i=j then B else LinearMap.id
lemma wield_at (Q : ActMap n G) (j : Fin n) (B : Module.End ℂ (WickPol G)) (v : Fin n → WickPol G) :
    wield Q j B v = Q (update v j (B (v j))) := by
  unfold wield; rw [MultilinearMap.compLinearMap_apply]; congr 1
  funext i; by_cases h : i=j <;> simp_all
lemma wield_switch (P : ActMap n G) (i j : Fin n) (h : i≠j) (B Q : Module.End ℂ (WickPol G)) : wield (wield P i B) j Q=wield (wield P j Q) i B := by
  ext1 v; simp only [wield_at]; congr 1; rw [update_of_ne h,update_of_ne h.symm, update_comm h]
lemma wield_zero_dep (P : ActMap n G) (i : Fin n) (B Q : Module.End ℂ (WickPol G)) : wield (wield P i B) i Q=wield P i (B.comp Q) := by ext1 v; simp [wield_at]

lemma path_wield (x y : E4) (hx : x≠y) (p : Probe G k) (i : Fin n) (Q : E4 → ActMap n G)
    (H : ∀ v,ContinuousAt (fun z => Q z v) 0) (v : Fin n → WickPol G) : ContinuousAt (fun z =>
      wield (Q z) i (eat p (x+z) y).toLinearMap v) 0 := by
  classical
  simp only [wield_at]; change ContinuousAt (fun z=>Q z (update _ i (eat p (x+z) y _))) 0
  obtain ⟨j,h⟩ := cap_exists (v i)
  simp_rw [all_bite p _ _ _ (cap_shelf _ h),bite_eval,MultilinearMap.map_update_sum, MultilinearMap.map_update_smul]
  unfold ContinuousAt; dsimp only; apply tendsto_finsetSum; intro a _; apply tendsto_finsetSum; intro b _; apply ContinuousAt.tendsto
  let q : Probe G a := coordinateLeg (keyAt a b)
  let f (z : E4) := x+z-y
  have hg : f 0∈away := by unfold f; rw [add_zero]; exact sub_ne_zero.mpr hx
  refine (show ContinuousAt (fun z : E4 => (legKernel p q (f z):ℂ)) 0 from ?_).smul (H _)
  exact Complex.continuous_ofReal.continuousAt.comp (((kernel_pole p q).diff _ hg).continuousAt.comp (show ContinuousAt f 0 from (continuousAt_const.add continuousAt_id).sub continuousAt_const))

lemma chorus (x : E4) (p : Probe G k) (i : Fin n) (Q : E4 → ActMap n G)
    (H : ∀ v,ContinuousAt (fun z => Q z v) 0) (v : Fin n → WickPol G) (h : v i∈ shelf G j) :
    Deep (4+k+j) M (fun z => wield (Q z) i (eat p (x+z) x).toLinearMap v) (fun z => wield (Q 0) i (singleBite j p z).toLinearMap v) := by
  classical
  let R (s) := 4+k+s
  let J (s) (z:E4) := fun t => Q z (update v i (singleBite s p t (v i)))
  have he (s) (z t) : J s z t = ∑ a, charge p s a t * Q z (update v i (MvPolynomial.pderiv (keyAt s a) (v i))) := by unfold J; rw [bite_eval,MultilinearMap.map_update_sum]; simp_rw [MultilinearMap.map_update_smul]; rfl
  have hp (s a) : Pole (R s) (charge p s a) := Pole.coord (kernel_pole p _) Complex.ofRealCLM
  have ht (s) : Echoes (R s) (fun z => J s z z) (J s 0) := by
    intro z hz; dsimp only
    simp_rw [he, Finset.smul_sum]; apply tendsto_finsetSum; intro a _
    let A t := Q t (update v i (MvPolynomial.pderiv (keyAt s a) (v i)))
    exact Echoes.mul (ray_little (R s) (hp s a).degree) (Echoes.regular (f:=A) (H _)) z hz
  have ha : Pole (R j) (J j 0) := by
    let f (a : Fin (legDim G j)) (z : E4) := charge p j a z * Q 0 (update v i (MvPolynomial.pderiv (keyAt j a) (v i)))
    have ht (s : Finset _) : Pole (R j) (∑ i∈s, f i) := by
      induction s using Finset.induction_on with
      | empty => rw [Finset.sum_empty]; exact Pole.zero _
      | @insert a s hh ih =>
        rw [Finset.sum_insert hh]; apply Pole.add _ ih
        exact (hp j a).coord (((1:ℂ →L[ℂ] ℂ).smulRight (Q 0 (update v i (MvPolynomial.pderiv (keyAt j a) (v i))))).restrictScalars ℝ)
    rw [show J j 0=∑ a : Fin (legDim G j), f a from funext fun y => (he j 0 y).trans (Finset.sum_apply y _ f).symm]; exact ht _
  have hO : (fun z : E4 => wield (Q z) i (eat p (x+z) x).toLinearMap v) = (fun z => ∑ a∈Finset.range j,J a z z)+(fun z => J j z z) := by
    ext1 z; rw [wield_at];
    change Q z (update v i (eat _ _ _ _)) = _; rw [all_bite _ _ _ _ h, add_sub_cancel_left, MultilinearMap.map_update_sum, Finset.sum_range_succ]; rfl
  have hE : Echoes (R j) (fun z => ∑ a∈Finset.range j,J a z z) 0 := by
    intro z hz; simp only [Finset.smul_sum]
    have hk := tendsto_finsetSum (Finset.range j) (fun a ha => (ht a).less (show R a< R j from Nat.add_lt_add_left (Finset.mem_range.mp ha) _) z hz)
    simpa using hk
  have hr : (fun z => wield (Q 0) i (singleBite j p z).toLinearMap v)=J j 0 := funext fun z => wield_at ..
  rw [hO,hr]
  exact Deep.bare (by simpa using Echoes.add hE (ht j)) ha

/-- In fact pure Echo; supply when second, strictly smaller leg takes the solo join. -/
lemma Deep.weaker {r j l : ℕ} {f K : Scatter} (H : Deep r l f K) (hr : r < j) : Deep j l f 0 := by
  obtain ⟨W,ht,V⟩ := H.silts
  exact ⟨Pole.zero _,W,ht,Echoes.less V hr⟩

lemma duet_path (x : E4) (p : Probe G k) (q : Probe G l) (Q : WickPol G →ₗ[ℂ] ℂ) (v : WickPol G) (h : v∈shelf G j)
    (r M) (hr : 8+k+l+j+j<M) : Deep r M (fun z => Q (eat q (x+z) x (eat p (x+z) x v))) 0 := by
  classical
  let T := Finset.range (j+1)
  have hp {l} (p : Probe G l) (s a) : Pole (4+l+s) (charge p s a) := Pole.coord (kernel_pole p _) Complex.ofRealCLM
  have hsum {ι : Type} (t : Finset ι) (f : ι→Scatter) (ht : ∀ i∈t,Deep r M (f i) 0) : Deep r M (fun z => ∑ i∈t,f i z) 0 := by
    convert! Deep.sum t f (fun _ => 0) ht using 1; simp; rfl
  let W (s b) := fun z=> Q (singleBite b q z (singleBite s p z v))
  rw [show (fun z => Q (eat q (x+z) x (eat p (x+z) x v)))=(fun z => ∑ s∈T,∑ b∈T,W s b z) from ?_]
  · apply hsum T; intro s hs; apply hsum T; intro b hb
    have hs := Finset.mem_range.mp hs
    have hb := Finset.mem_range.mp hb
    unfold W; simp only [bite_eval,map_sum,map_smul,Derivation.map_smul,Finset.smul_sum]
    refine hsum Finset.univ _ (fun i _ => hsum Finset.univ _ (fun a _ => ?_))
    let U := Q (MvPolynomial.pderiv (keyAt b a) (MvPolynomial.pderiv (keyAt s i) v))
    change Deep r M (fun z => charge p s i z*(charge q b a z * U)) 0
    exact Deep.carried (Silt.twice (hp p s i) ((hp q b a).coord (((1:ℂ →L[ℂ] ℂ).smulRight U).restrictScalars ℝ)) (by omega) (by omega)) (by omega) r
  ext1 z
  rw [all_bite p _ _ _ h, map_sum]; simp_rw [all_bite q _ _ _ (upper_shelf h p _)]
  rw [map_sum]; simp_rw [map_sum,add_sub_cancel_left]; rfl
end YM.Maxwell.Free
