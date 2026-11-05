import YM.Extra.MULTISOURCE_TRAJECTORIES.Blocks
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Clinic
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Panes
import YM.Progress.DIRECTED_RECIPE.Imports
import YM.Push.RELAY_MARK.Transit

/-! # Winding-support sensitivities in output price currency -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure Planned.AtomRegular.Foliage MultiNext.SignedSource WardBin.Lies
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {g : outfit G f c} {X : Support f} {Y : Support c} {Q M C t r x : ℝ} {I : Type}
    {A : Stores S} {n j l : ℕ} {w : Prices G I} {u : ℝ} {D : Slab G c l} {o : Site f} {i : Bond f}

def heft (n : ℕ) (X : Support f) (P B : BudgetPoint) := ((2+(breadth B X:ℝ))^P.power)^n
lemma heft_one (n : ℕ) (X : Support f) (P B : BudgetPoint) : 1 ≤ heft n X P B := one_le_pow₀ (one_le_pow₀ (by have h := Nat.cast_nonneg (α:=ℝ) (breadth B X); linarith))
lemma heft_bounds (S : StepData c f) (ho : o∈X) (hi : i.1∈inspected X) (hj : j ≤ n) : (spine P.power (S.ratio.parent i.1) (S.ratio.parent o))^j ≤ heft n X P B := by
  refine le_trans (pow_le_pow_right₀ (spine_one ..) hj) (pow_le_pow_left₀ (spine_pos ..).le (pow_le_pow_left₀ (by positivity) ?_ _) n)
  have h : (separation (S.ratio.parent i.1) (S.ratio.parent o):ℝ) ≤ breadth B X+1 := by
    exact_mod_cast (Work.E04.parent_separation S.ratio i.1 o).trans (Nat.add_le_add_right (close_enough ho hi) 1)
  linarith

def segment (n : ℕ) (X : Support f) (P B : BudgetPoint) (Q M v : ℝ) := ((clinicFee n Q + M)*v^2*heft n X P B)/B.threshold
lemma segment_nn (n : ℕ) (X : Support f) (P B : BudgetPoint) {Q M v : ℝ} (hQ : 1 ≤ Q) (hM : 1 ≤ M) : 0 ≤ segment n X P B Q M v := by
  unfold segment; have hh : 0 ≤ clinicFee n Q := le_trans (by positivity) (clinicFee_le n (zero_le_one.trans hQ)); have hy : 0 ≤ heft n X P B := zero_le_one.trans (heft_one ..); have := B.threshold_pos; positivity

def ample (n : ℕ) (X : Support f) (P B : BudgetPoint) (Q M C x : ℝ) := M*(C*2)+segment n X P B Q M (loom P (reach x) C)
lemma ample_one (n : ℕ) (X : Support f) (P B : BudgetPoint) {Q M C x : ℝ} (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hC : 1 ≤ C) : 1 ≤ ample n X P B Q M C x :=
  (one_le_mul_of_one_le_of_one_le hM (one_le_mul_of_one_le_of_one_le hC one_le_two)).trans (le_add_of_nonneg_right (segment_nn n X P B hQ hM))

section travel
variable (i : Bond f) (hT : Canvas P (S.ratio.parent i.1) (reach x) V (g i) n C) (h : Matins T F B.power t M) (ho : o∈X) (hi : i.1∈inspected X) (hh : P.power ≤ B.power)
    (hC : 1≤C) (hM : 1≤M) (ht : P.threshold ≤ 2*B.threshold) (h' : ∀ j, P.dirBound (S.ratio.parent o) (D j)) (hl : l ≤ n) (hr : loom P (reach x) C ≤ 1)
include hT h hh ho hi hC hM ht h' hl hr
lemma woody_price (hj : 0 < j) (hJ : j ≤ n) (v : Fin j→ Panels l) (he : ∀ k, ‖v k‖ ≤ 1) : let z := launch V (S.ratio.parent i.1) (reach x) (g i) D
    ‖woody T F (iteratedFDeriv ℝ j z 0 v) i‖ ≤ M*(C*2)*Lyre.width B o i + M*(loom P (reach x) C)^2 * heft n X P B := by
  intro z; let b := iteratedFDeriv ℝ j z 0 v; let H := heft n X P B; have hH : 1 ≤ H := heft_one ..
  have hp := P.threshold_pos
  by_cases hx : j=1
  · refine (h.stage b i o (by positivity) (hT.individual h' hC hl hJ hj v he hh (Or.inl hx))).trans (le_add_of_le_of_nonneg ?_ (by positivity))
    unfold Lyre.width; unfold spine; have h₁ := spine_pos B.power i.1 o
    calc
      _ ≤ M*(C*(2*B.threshold))*spine B.power i.1 o := by change _*_*spine _ _ _ ≤ _; gcongr
      _ = _ := by unfold spine; ring
  let Q := loom P (reach x) C
  have h₀ : 0 ≤ Q := by unfold Q loom; positivity
  have hB : ‖b‖ ≤ Q^2*H := (hT.cost h' hC hl hJ hj v he).trans (mul_le_mul (pow_le_pow_of_le_one h₀ hr (by omega : 2 ≤ j)) (heft_bounds S ho hi hJ) (pow_nonneg (spine_pos ..).le _) (sq_nonneg Q))
  refine le_trans (h.stage b i i.1 (t:=Q^2*H) (by positivity) (fun j => ((norm_le_pi_norm ..).trans hB).trans
    (le_mul_of_one_le_right (by positivity) (spine_one ..)))) ?_
  rw [spine_self, mul_one,← mul_assoc]; exact le_add_of_nonneg_left (by positivity [Lyre.width_pos B o i])
end travel
namespace Museum
variable [Fintype I] (k T V u w) (a : Museum F x A X Y I) (g D)
abbrev wind (i : Bond f) := converses V (S.ratio.parent i.1) (reach x) (g i) D (a.extra (g i) u w)
abbrev overture (z : Panels l) := a.overt T k V u w g (journey V _ D z) w
variable {k T V u w g D}

variable (hT : Act T F x k n r Q) (h : Panes S V x X P n C g) (h' : Matins T F B.power t M) (ho : o∈X)
    (hQ : 1≤Q) (hC : 1≤C) (hM : 1≤M) (hn : 2≤n) (hl : l ≤ n) (ht : P.threshold=temp x) (ht' : temp x ≤ 2*B.threshold) (hpow : P.power ≤ B.power)
    (hs : loom P (reach x) C ≤ 1) (hr : loom P (reach x) C ≤ r) (hw : ∀ g : Site c → G.El, ‖a.extra g u w‖ ≤ loom P (reach x) C)
    (hd : ∀ j, P.dirBound (S.ratio.parent o) (D j))
include hT h hQ hC hn hl ht hs hr hw hd
lemma reprise_at (hi : Mom.needed X i) : let Z := a.wind V g w u D i; let Y := reply T F x k (g i) i ∘ Z
    ContDiffAt ℝ n Y 0 ∧ ∀ j > 0, j ≤ n → ∀ v : Fin j → Panels l, (∀ i, ‖v i‖ ≤ 1) →
      let b := iteratedFDeriv ℝ j (launch V (S.ratio.parent i.1) (reach x) (g i) D) 0 v
      ‖iteratedFDeriv ℝ j Y 0 v‖ ≤ ‖woody T F b i‖ + clinicFee n Q*(loom P (reach x) C)^2*(spine P.power (S.ratio.parent i.1) (S.ratio.parent o))^j := by
  intro Z Y
  obtain ⟨hz,hz'⟩ := timesEcho (h.fits _ hi) hT ht hn hd hC hl hQ hs hr (hw (g i))
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond f => G.Color) i
  let H := (G.adjoint ((g i (S.ratio.parent i.1))⁻¹)).toContinuousLinearMap
  refine ⟨(H.comp L).contDiff.contDiffAt.comp (f:=echo T F x k ∘ Z) _ hz,fun j hj hj' v hv => ?_⟩
  rw [show Y=(H.comp L) ∘ (echo T F x k ∘ Z) from rfl,(H.comp L).iteratedFDeriv_comp_left hz (Nat.cast_le.mpr hj')]
  intro b
  let p := iteratedFDeriv ℝ j (echo T F x k ∘ Z) 0 v
  change ‖G.adjoint _ (p i)‖ ≤ _; rw [G.norm_adjoint]
  calc
    _ ≤ ‖woody T F b i‖ + ‖(p-woody T F b) i‖ := by change _ ≤ _ + ‖p i - _‖; simpa using norm_add_le (woody T F b i) (p i-woody T F b i)
    _ ≤ _ := add_le_add_right ((norm_le_pi_norm (p-woody T F b) i).trans (hz' j hj hj' v hv)) _

omit hT h hQ hC hn hl ht hs hr hw hd in
lemma overture_eq (z : Panels l) : a.overture T k V g w u D z i = if Mom.needed X i then reply T F x k (g i) i (a.wind V g w u D i z) else 0 := by
  simp only [overture,overt]; split; swap; · rfl
  unfold pane wind converses enters; rw [launch_zero]; rfl

include h' hM ho ht' hpow
lemma reprise : let z := a.overture T k V g w u D
    ContDiffAt ℝ n z 0 ∧ ∀ j > 0, j ≤ n → ∀ v : Fin j → Panels l, (∀ i, ‖v i‖ ≤ 1) →
      Lyre.Sized (ample n X P B Q M C x) (iteratedFDeriv ℝ j z 0 v) B o := by
  intro z
  have H i hi := a.reprise_at hT h hQ hC hn hl ht hs hr hw hd (i:=i) hi
  have hz : ContDiffAt ℝ n z 0 := by
    apply contDiffAt_pi.mpr; intro i; simp only [z,overture_eq]; split; exact (H _ ‹_›).1; exact contDiffAt_const
  refine ⟨hz,fun j hj hj' v hv => ⟨zero_le_one.trans (ample_one n X P B hQ hM hC),fun i => ?_⟩⟩
  let L := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond f => G.Color) i
  rw [show iteratedFDeriv ℝ j z 0 v i = iteratedFDeriv ℝ j (fun y => z y i) 0 v from congrArg (fun T : Panels l [×j]→L[ℝ] G.Color => T v) (L.iteratedFDeriv_comp_left hz (Nat.cast_le.mpr hj')).symm]
  simp only [z,overture_eq]; split; swap; · rw [iteratedFDeriv_const_of_ne (Nat.ne_of_gt hj)]; change ‖(0:G.Color)‖ ≤ _; exact norm_zero.le.trans (mul_nonneg (zero_le_one.trans (ample_one n X P B hQ hM hC)) (Lyre.width_pos ..).le)
  next hi =>
  have hnn : 0 ≤ clinicFee n Q := (mul_nonneg (by norm_num) (zero_le_one.trans hQ)).trans (clinicFee_le n (zero_le_one.trans hQ))
  have he₀ : B.threshold ≤ Lyre.width B o i := le_mul_of_one_le_right B.threshold_pos.le (spine_one B.power i.1 o)
  refine ((H i hi).2 j hj hj' v hv).trans ?_
  have hi' : i.1∈inspected X := Finset.mem_union_left _ hi.1
  apply (add_le_add (woody_price _ (h.fits _ hi) h' ho hi' hpow hC hM (ht.symm ▸ ht') hd hl hs hj hj' v hv)
    (mul_le_mul_of_nonneg_left (heft_bounds (B:=B) S ho hi' hj') (mul_nonneg hnn (sq_nonneg _)))).trans
  unfold ample; rw [add_mul,add_assoc]; apply add_le_add_right
  apply le_trans _ (mul_le_mul_of_nonneg_left he₀ (segment_nn n X P B hQ hM))
  unfold segment; rw [div_mul_cancel₀ _ B.threshold_pos.ne']; exact le_of_eq (by ring)
end Museum
end YM.PhysicalNext.JointLoad.Heir
