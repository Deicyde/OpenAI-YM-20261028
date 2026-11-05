import YM.FullVolume.Table.Salute
/-! Measure norm actual ℓ¹-H. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Urns
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration RG.Shoot
open Push.PriceCompiler Push.AbsoluteSums Progress.DirectedRecipe Time UVNext.CouplingReset Ovens Ovens.Pipes
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}{c:Side} {S:Price G c}
local notation "X"=>arena S
variable (f:arena S)
-- norm choice equality by leaf_min. Cost epochs
abbrev Sells (f:arena S) (v:ℝ):Prop:=Cash S.p f.val (v*S.b) (v*S.k)
lemma can : ∃ v, Sells f v:=by
  obtain ⟨u,v,h⟩:= f.property; refine ⟨max (u/S.b) (v/S.k), more h ((div_le_iff₀ S.b0).mp (le_max_left ..)) ((div_le_iff₀ S.k0).mp (le_max_right ..))⟩
def rate (f : arena S):= sInf {v|Sells f v}
variable {f} {v:ℝ}
lemma sells_nn (h:Sells f v):0≤v:=by
  obtain ⟨y,-,hy⟩:= h.2.2.1
  exact nonneg_of_mul_nonneg_left (budget_nonneg (hy 0)) S.b0
lemma sells_r (h:Sells f v):rate f ≤ v:=csInf_le ⟨0,fun _ hx=> sells_nn hx⟩ h
lemma rate_nn (f:arena S):0≤ rate f:= le_csInf (can f) fun i hi=> sells_nn hi
lemma past (h:rate f<v): Sells f v:= by
  obtain ⟨t,ht,hx⟩:= exists_lt_of_csInf_lt (can f) h
  exact more ht (mul_le_mul_of_nonneg_right hx.le S.b0.le) (mul_le_mul_of_nonneg_right hx.le S.k0.le)
-- use sSup each, no topology prices
lemma entered (f:arena S): Sells f (rate f) := by
  let Y:=S.p; let A:= issue Y f.val
  obtain ⟨d,k,hF,hK,hc,h⟩:=f.property; obtain ⟨w,hw,H⟩:= hc; obtain ⟨s,hS,h⟩:= h
  have hx (i:ℕ) : ∃ z,Y.supBounds (A.reg i).site (A.reg i).support (A.E i) z ∧ ∀ v:ℝ, Y.supBounds (A.reg i).site (A.reg i).support (A.E i) v→ z≤v:= by
    let f : ℝ→Prop:= Y.supBounds (A.reg i).site (A.reg i).support (A.E i)
    let z:Set ℝ:= {v|f v}
    have hx : z.Nonempty:= ⟨_,hw i⟩; have ht : (0:ℝ) ∈lowerBounds z:= fun _ h=> h.1
    refine ⟨sInf z,⟨le_csInf hx ht,?_⟩,fun u hu=> csInf_le ⟨0,ht⟩ hu⟩
    intro U hU l hl he; exact le_csInf hx fun _ hb=> hb.2 U hU l hl he
  choose a ha hz using hx
  have he (i:ℕ):∃ z,(0≤z∧∀ U,‖A.K i U‖ ≤ z) ∧ ∀ v:ℝ,(0≤v∧∀ U, ‖A.K i U‖≤v)→ z≤v:=by
    let Z:Set ℝ:={v|0≤v∧∀ U,‖A.K i U‖≤v}; have hx : Z.Nonempty:= ⟨_,hS i⟩; have hv:(0:ℝ)∈lowerBounds Z:= fun i hi=> hi.1
    exact ⟨sInf Z,⟨le_csInf hx hv,fun i=> le_csInf hx fun i' hi=> hi.2 i⟩,fun v hv'=> csInf_le ⟨0,hv⟩ hv'⟩
  choose b hb hu using he
  refine ⟨hF,hK,⟨a,ha,fun i=>?_⟩,⟨b,hb,fun i=>?_⟩⟩
  · apply budget_of_sum
    · intro j; split; exact mul_nonneg (Real.exp_nonneg _) (ha j).1; rfl
    intro t
    apply (div_le_iff₀ S.b0).mp; refine le_csInf (can f) fun x h=>?_
    obtain ⟨a,hb,h⟩:= (show Sells f x from h).2.2.1
    apply (div_le_iff₀ S.b0).mpr
    apply le_trans (Finset.sum_le_sum ?_) (budget_sum (h i) t); intro i _; split; exact mul_le_mul_of_nonneg_left (hz i _ (hb i)) (Real.exp_nonneg _); rfl
  apply budget_of_sum
  · intro j; split; exact mul_nonneg (Real.exp_nonneg _) (hb j).1; rfl
  intro t; apply (div_le_iff₀ S.k0).mp; refine le_csInf (can f) fun x h=>?_
  obtain ⟨a,hb,h⟩:= (show Sells f x from h).2.2.2
  apply (div_le_iff₀ S.k0).mpr
  exact (Finset.sum_le_sum (fun j _=> by split; exact mul_le_mul_of_nonneg_left (hu j _ (hb j)) (Real.exp_nonneg _); rfl)).trans (budget_sum (h i) t)
lemma rate_iff : rate f ≤ v ↔ Sells f v:= ⟨fun h=> more (entered f) (mul_le_mul_of_nonneg_right h S.b0.le) (mul_le_mul_of_nonneg_right h S.k0.le),sells_r⟩
lemma joined (f g:arena S) : rate (f+g) ≤ rate f+rate g:= by
  apply sells_r; unfold Sells; rw [add_mul,add_mul]; exact addP (entered f) (entered g)
lemma rate_smul_le (f:arena S)(b:ℝ) : rate (b • f)≤ ‖b‖*rate f:=by apply sells_r; unfold Sells; rw [mul_assoc,mul_assoc]; exact movingS b (entered f)
lemma rate_smul (f:arena S)(b:ℝ) : rate (b • f)= ‖b‖*rate f:=by
  refine le_antisymm (rate_smul_le _ _) ?_; by_cases he:b=0
  · rw [he,norm_zero,zero_mul]; exact rate_nn _
  have h:= rate_smul_le (b • f) b⁻¹; rw [inv_smul_smul₀ he] at h; exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by rw [norm_inv, ← mul_assoc,mul_inv_cancel₀ (norm_pos_iff.mpr he|>.ne'),one_mul])
def lengthP (S:Price G c) : Seminorm ℝ (arena S):= Seminorm.of rate joined (fun b f=>rate_smul f b) -- name
-- **irreducible copy** avoids inherited uniformity on submodule with inherited pointwise topology! persistent.
def Show (S:Price G c): Type:= arena S
namespace Show
-- use via Equality
instance (S: Price G c) : AddCommGroup (Show S) := inferInstanceAs (AddCommGroup (arena S))
instance (S: Price G c) : Module ℝ (Show S):= inferInstanceAs (Module ℝ (arena S))
noncomputable instance (S:Price G c): SeminormedAddCommGroup (Show S) :=
  { (inferInstance : AddCommGroup (Show S)), (Seminorm.toAddGroupSeminorm (lengthP S)).toSeminormedAddCommGroup with }
noncomputable instance (S:Price G c): NormedSpace ℝ (Show S) where
  __ := (show Module ℝ (Show S) from inferInstance)
  norm_smul_le r f:= show rate _ ≤ _ from (rate_smul (show arena S from f) r).le
variable (f:Show S)
def peek : Show S≃ₗ[ℝ] arena S:= LinearEquiv.refl _ _
lemma height (f:Show S): ‖f‖=rate (peek f):=rfl
abbrev proper (f:Show S):= issue S.p (peek f).val
lemma budget (f:Show S)(b:ℝ):‖f‖≤ b ↔ Cash S.p (peek f).val (b*S.b) (b*S.k):= rate_iff
end Show
end YM.FullVolume.Urns
