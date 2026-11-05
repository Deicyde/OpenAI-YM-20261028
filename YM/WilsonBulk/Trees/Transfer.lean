import YM.WilsonBulk.Trees.Laminate
import YM.WilsonBulk.Vacuum.HessRates

/-! # quantitative input-data usage for fluctuating covariance.

Use `packing_bill` below *before* producing delay/coarsening widths, after J thickness choices.
At difference on a common cut, pay `flat` precision only -- no amplitude/A0 continuity,
`Φ` or reconstruction estimate needed. This depends only on κ and Hessians even though the
joint upper completer technologies cost bounds are themselves priced with explicit tags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Finset Precision Exterior Stationary Audience Matrix FreeResolvent Tree
open Work.F08 Lifted Primitives.TwoWave
open Progress.ClassicalKin Progress.ClassicalKin.Tent
open scoped Topology BigOperators Matrix Classical

section identity
variable {c f : Side} {G : Gauge} {S : StepData c f} {T : Forest S.ratio}
lemma rectangle_inv {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] (X Y H L : Matrix a a ℝ)
    (M : Matrix b a ℝ) (Q : Matrix a b ℝ) (A B : Matrix b b ℝ)
    (h : X*H=1) (hp : L*Y=1) (hx : Q*A*M=X) (hv : Q*B*M=Y) :
    M*H*Q-M*L*Q=(M*L*Q)*(B-A)*(M*H*Q) := by
  have ht : Q*(B-A)*M=Y-X := by rw [Matrix.mul_sub,Matrix.sub_mul,hv,hx]
  have he : L*(Q*(B-A)*M)*H=H-L := by rw [ht,Matrix.mul_sub, hp,Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_one]
  calc _ = M*((H-L)*Q) := by simp only [Matrix.mul_assoc,Matrix.sub_mul,Matrix.mul_sub]
       _ = _ := by rw [← he]; simp only [Matrix.mul_assoc]

lemma packed_diff (T : Forest S.ratio) (P Q : Bed) (h : Bid.Larger (G:=G) S)
    {η : ℝ} (hη : 0< η) (hP : Gap (P.metric.acts f) η) (hQ : Gap (Q.metric.acts f) η) :
    covariance G S T P.metric - covariance G S T Q.metric = covariance G S T Q.metric *
      patron G (Precision.K (Q.metric.acts f)-Precision.K (P.metric.acts f)) * covariance G S T P.metric := by
  have hx := tree_laws T P.metric h hη hP (le_refl 0)
  have hv := tree_laws T Q.metric h hη hQ (le_refl 0)
  unfold covariance reduce
  convert rectangle_inv _ _ _ _ (insertion (plant T (G:=G))) (insertion (plant T (G:=G))).transpose (fullMatrix G S P.metric)
    (fullMatrix G S Q.metric) (?_ : treeMatrix G S T P.metric*treeInverse G S T P.metric 0=1)
    (?_ : treeInverse G S T Q.metric 0* treeMatrix G S T Q.metric =1) (insertion.compress (plant T) _) (insertion.compress (plant T) _) using 2
  · rw [wired_full G S Q,wired_full G S P, add_sub_add_right_eq_sub]; simp only [match_tensor]; congr 1; ext i j; unfold tensor; simp only [Matrix.of_apply,Matrix.sub_apply]; split <;> simp
  · simpa using hx.2
  simpa using hv.1
end identity

variable {P : Patch} {K : KernelChoices} {G : Gauge}

structure Serves (G : Gauge) (T : Model P K) (B : Bed) (σ M : ℝ) : Prop where
  width : (fluct G T B).strip σ M
  covers {c f:Side} (v : f.val=c.val*P.L.val) (h : Bid.Larger (G:=G) (data v K)) :
    Seen c (splitCo (data v K).ratio _) (splitCo (data v K).ratio _) (fluct G T B)
      (covariance G _ (spreadForest T v) B.metric)

-- θ cap input ledger, e.g. A.J m, post-cost independent of any cut & period.
lemma packing_bill (G : Gauge) (j : ℕ) (K : KernelChoices) (σ ε Ω : ℝ)
    (hσ : 0<σ) (hε : 0<ε) (hΩ : 0≤ Ω) :
    ∃ η, 0 < η ∧ ∀ P : Patch, P.J=j → P.Branches K G →
      ∀ T : Model P K, ∃ C, 0 ≤ C ∧ ∀ B : Bed, ∀ p D, B.metric.strip (inch P.L*σ) Ω →
        (∀ n, Floor B p n ε D) → Serves G T B η C := by
  obtain ⟨η,hη,H⟩:= uniform_backing G j K σ ε Ω hσ hε hΩ
  refine ⟨η,hη,fun P hJ hP T=>?_⟩
  obtain ⟨A,hA,h⟩:= H P.L
  obtain ⟨B,hB,hK⟩:= (Stamped.aimed G T).bound η
  refine ⟨_,?_,fun Y p D hv hw=>⟨fluct_ready G T Y (h P hJ rfl hP Y p D hv hw).1 hη.le hK,
    fun v hy=> fluct_poses G T Y (h P hJ rfl hP Y p D hv hw).1 hη.le hε (hw _) v hy (Classical.arbitrary _) ((h P hJ rfl hP Y p D hv hw).2 _ _ _ _)⟩⟩
  positivity

lemma Seen.difference {A B α β : Type} {U V : Matrix A B ℝ} {c : Side}
    {x : A ≃ Co c α} {y : B ≃ Co c β} {σ M W : ℝ} {R Q : Row α β}
    (h : Seen c x y R U) (he : Seen c x y Q V) (hR : R.strip σ M) (hQ : Q.strip σ W) (hσ : 0≤σ) :
    Seen c x y (minusRows R Q) (U-V) := by
  unfold Seen at *; rw [h,he,acts_minus hσ hR hQ]; rfl

lemma packing_cost (h : P.Branches K G) (T : Model P K) (B V : Bed)
    {σ θ C D M W : ℝ} (hσ : 0≤ σ) (hθ : 0 ≤ θ) (p : Clip) {ε A Z : ℝ} (hε : 0< ε) (hw : 0≤ W)
    (hB : ∀ n, Floor B p n ε A) (hV : ∀ n, Floor V p n ε A)
    (hM : B.metric.strip θ M) (hZ : V.metric.strip θ Z)
    (hC : Serves G T B σ C) (hD : Serves G T V σ D)
    (hW : (minusRows (actionKernel B.metric) (actionKernel V.metric)).strip σ W) :
    (minusRows (fluct G T V) (fluct G T B)).strip σ
      (((Fintype.card (Co P.L (Loc G 1)):ℝ)*(Fintype.card (Co P.L (Loc G 1)))*(Fintype.card PotentialForm))*W*C*D) := by
  let I:= minusRows (actionKernel B.metric) (actionKernel V.metric)
  let J:= fineColor G (reblock P.L I)
  let W' : ℝ := Fintype.card PotentialForm * W
  have ht : J.strip σ W':= painted_strip _ _ _ _ (reblock_price hσ hW) (by unfold W'; positivity)
  let X := composeRows (composeRows (fluct G T B) J) (fluct G T V)
  change I.strip σ W at hW
  have hX := strip_compose hσ (strip_compose hσ hC.width ht) hD.width
  let n (i : ℕ) : Side:=⟨i+1,Nat.zero_lt_succ _⟩
  have hn : Tendsto (fun i => (n i).val) atTop atTop := tendsto_atTop_mono (fun i => (show i≤ i+1 by omega)) tendsto_id
  suffices he : minusRows (fluct G T V) (fluct G T B)=X by rw [he]; convert hX using 1; unfold W'; ring
  obtain ⟨d,hd⟩:= RealSlice.dock_larger P K h
  let i₀:= d
  apply many_acts (Row.rights _ _ (strip_minus hD.width hC.width) hσ) (Row.rights _ _ hX hσ) hn
  filter_upwards [hn.eventually_ge_atTop d] with i hi
  let S:= dock P K (n i); let F:=spreadForest T (f:=below P (n i)) (c:=n i) rfl
  have hS : Bid.Larger S (G:=G):= hd _ hi
  have hc : Seen (n i) (splitCo S.ratio _) (splitCo S.ratio _) (fluct G T B) (covariance G S F B.metric) :=
    hC.covers (f:=below P (n i)) (c:=n i) rfl hS
  have hq : Seen (n i) (splitCo S.ratio _) (splitCo S.ratio _) (fluct G T V) (covariance G S F V.metric) :=
    hD.covers (f:=below P (n i)) (c:=n i) rfl hS
  let b := below P (n i)
  have hr : Seen (n i) (splitCo S.ratio _) (splitCo S.ratio _) J (patron G (Precision.K (B.metric.acts b)-Precision.K (V.metric.acts b))) := by
    have he : Seen (n i) (splitCo S.ratio _) (splitCo S.ratio _) (reblock P.L I) (I.acts b) := reblock_periods S.ratio hσ hW
    have hy : I.acts b = _ := (acts_minus hθ (actionKernel_strip hθ hM) (actionKernel_strip hθ hZ) b).trans
      (congr_arg₂ Sub.sub (actionKernel_acts hθ hM b) (actionKernel_acts hθ hZ b))
    have hx := Seen.fine G he; unfold Seen; exact Eq.trans (congrArg (patron G (j:=1)) hy.symm) hx
  have he := Seen.chain (Seen.chain hc hr hC.width ht hσ) hq (strip_compose hσ hC.width ht) hD.width hσ
  erw [(Seen.difference hq hc hD.width hC.width hσ).equal]
  erw [Seen.equal he]
  apply congr_arg; exact packed_diff F _ _ hS hε ⟨fun v=>((hV _).uniform.1 v).1⟩ ⟨fun v=>((hB _).uniform.1 v).1⟩

end YM.WilsonBulk
