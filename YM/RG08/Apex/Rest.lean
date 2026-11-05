import YM.RG08.Crossing.Caper
/-! # Limit selections (off-admission unspecified), quantitative
 weight on the declared admission. Received on actual underlying rows. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums UVExtension.Free
open scoped BigOperators Topology Real Classical
variable {I : Type} {u : I→Windows} {r e : ℕ}

def apex {X : Type} [TopologicalSpace X] [Zero X] (F : ℕ→X) := if h:∃ x,Tendsto F atTop (𝓝 x) then h.choose else 0
lemma apex_win {X : Type} [TopologicalSpace X] [Zero X] {F : ℕ→X} (h:∃ x,Tendsto F atTop (𝓝 x)) : Tendsto F atTop (𝓝 (apex F)) := by unfold apex; rw [dif_pos h]; exact h.choose_spec
lemma charge_stop {α : Type} {w U : α→ℝ} (hp : 0≤w) {F : ℕ→α→ℝ} (h : Tendsto F atTop (𝓝 U)){A} (he: ∀ᶠ i in atTop, Charge w (F i) A) : Charge w U A := by
    let T i:=w i*‖U i‖; have hu i : 0≤T i:=mul_nonneg (hp i) (norm_nonneg _)
    have hh s : ∑ i∈s,T i ≤ A := le_of_tendsto (tendsto_finsetSum s fun i _=> (tendsto_pi_nhds.mp h i).norm.const_mul (w i)) (he.mono fun i hi=> ((hi.2.1.sum_le_tsum _ (fun j _=> hi.1 j)).trans hi.2.2))
    have ht:= summable_of_sum_le hu hh
    exact ⟨hu,ht,ht.tsum_le_of_sum_le hh⟩
lemma skating {α : Type} {V : ℕ→ Shale α r} {w A : ℝ} {g : ℕ→ℝ} {ℓ}
    (h : ∀ i, ℓ ≤ i → Glow (V i) w A)(hp : ∀ i, ℓ ≤ i → ∀ j≥i, Glow (V i-V j) w (g i)) (hw : 0 ≤ w)(hg : Tendsto g atTop (𝓝 0)) : Glow (apex V) w A ∧ Tendsto V atTop (𝓝 (apex V)) ∧ ∀ i≥ℓ, Glow (V i-apex V) w (g i) := by
  have hc (i) : CauchySeq (fun j=> V j i) := by
    apply Metric.cauchySeq_iff'.mpr; intro ε he
    obtain ⟨N,hN,hh⟩ := ((eventually_ge_atTop ℓ).and (hg.eventually (gt_mem_nhds he))).exists
    refine ⟨N,fun j hj => ?_⟩
    rw [dist_comm,dist_eq_norm_sub]; exact ((le_mul_of_one_le_left (norm_nonneg _) (ling_one hw i)).trans (budget_single (hp N hN _ hj) _)).trans_lt hh
  choose U hU using fun i=> cauchySeq_tendsto_of_complete (hc i)
  have hh:=apex_win (F:=V) ⟨U,tendsto_pi_nhds.mpr hU⟩
  exact ⟨charge_stop (fun i=>(ling_pos _ _).le) hh ((eventually_ge_atTop ℓ).mono fun i hi=> h i hi),hh,fun i hi=> charge_stop (fun i=>(ling_pos _ _).le) (tendsto_const_nhds.sub hh) ((eventually_ge_atTop _).mono (hp i hi))⟩
variable {S : Chain}

-- unify directed limits
-- here parameter α not variant
lemma Both.landed {α : Type} {F : ℕ→ℕ→ Shale α r} {σ : ℕ→ℝ} {t:ℕ}(h : Both (Wings.menu (u:=u) S) (Wings.chop S (1/4)) (fun i:Wings u t=> F i.N i.i) (fun i=> F i.M i.i) (fun i=>σ i.i))(he : 0 ≤ σ) :
    Both (Wings.menu (u:=u) S) (Wings.chop S (1/4)) (fun i:Wings u t=> F i.N i.i) (fun i=> apex (fun N=> F N i.i)) (fun i=>σ i.i) := by
  obtain ⟨D,⟨A,p,hA,H⟩,hx⟩:=h.fresh; obtain ⟨C,⟨B,q,hB,H'⟩,hv⟩:=h.moves
  have hh (s : Wings u t) (N)(hN : s.i+t ≤ N) := show Glow (F N s.i) (σ s.i) (A*(s.menu S)^p) from glow_less (hx {s with N:=N,M:=N,cut:=hN,side:=le_rfl}) le_rfl (by rw [Pi.one_apply,mul_one]; exact (H _).2)
  have ht (s : Wings u t) : Glow (apex (fun n=>F n s.i)) (σ s.i) (A*(s.menu S)^p) ∧ Tendsto (fun n=> F n s.i) atTop (𝓝 (apex fun n=>F n s.i)) ∧ ∀ N ≥ s.i+t,Glow (F N s.i-apex (fun n=>F n s.i)) (σ s.i) (B*(s.menu S)^q*gain S.S (1/4) s.i N) := skating (hh s) (fun N hN M hM=> glow_less (hv {s with N:=N,M:=M,side:=hM,cut:=hN}) le_rfl (mul_le_mul_of_nonneg_right (H' _).2 (gain_pos ..).le)) (he _) (by simpa using (tendsto_gain S.S (v:=1/4) (by norm_num) s.i).const_mul (B*(s.menu S)^q))
  let V := Wings.menu (u:=u) (r:=t) S; have hw s : Weighed V (V^s):= Weighed.power V (Wings.sh S) _
  refine ⟨h.fresh,⟨_,(Weighed.constant V hA).times (hw p),fun i=>?_⟩,⟨_,(Weighed.constant V hB).times (hw q),fun i=>?_⟩⟩
  · rw [Pi.mul_apply,Pi.pow_apply,Pi.one_apply,mul_one]; exact (ht i).1
  rw [Pi.mul_apply,Pi.pow_apply]; exact (ht i).2.2 i.N i.cut
lemma highRate {α β : ℕ→Type} [∀ i,Fintype (α i)] [∀ i,Fintype (β i)] {F : ∀ (_ : ℕ) (i:ℕ),Row (α i) (β i)} {σ:ℕ→ℝ} {t:ℕ}(hp : ∀ i, 0<σ i) (h : RowBoth (Wings.menu (u:=u) S) (Wings.chop S (1/4)) (fun i:Wings u t=> F i.N i.i) (fun i=> F i.M i.i) (fun i=>σ i.i)) :
    RowBoth (Wings.menu (u:=u) S) (Wings.chop S (1/4)) (fun i:Wings u t=> F i.N i.i) (fun i=> apex (fun N=> F N i.i)) (fun i=>σ i.i) := by
  obtain ⟨D,⟨A,p,hA,H⟩,hx⟩:=h.fresh; obtain ⟨C,⟨B,q,hB,H'⟩,hv⟩:=h.moves
  have hh (s : Wings u t) (N)(hN : s.i+t ≤ N) := show (F N s.i).strip (σ s.i) (A*(s.menu S)^p) from strip_mono (hx {s with N:=N,M:=N,cut:=hN,side:=le_rfl}) le_rfl (by rw [Pi.one_apply,mul_one]; exact (H _).2)
  have ht (s : Wings u t) : Received (fun n=> F n s.i) (apex (fun n=>F n s.i)) (σ s.i) (A*(s.menu S)^p) ∧ ∀ N ≥ s.i+t,(F N s.i-apex (fun n=>F n s.i)).strip (σ s.i) (B*(s.menu S)^q*gain S.S (1/4) s.i N) := by
    obtain ⟨f,hf,hv'⟩:= cauchy_row_rate (X:=fun n=> F n s.i) (fun i=> B*(s.menu S)^q*gain S.S (1/4) s.i i) (hp _) ((eventually_ge_atTop _).mono (hh s)) (fun N hN M hM=> strip_mono (hv {s with N:=N,M:=M,side:=hM,cut:=hN}) le_rfl (mul_le_mul_of_nonneg_right (H' _).2 (gain_pos ..).le)) (by simpa using (tendsto_gain S.S (v:=1/4) (by norm_num) s.i).const_mul (B*(s.menu S)^q))
    rw [tendsto_nhds_unique (apex_win ⟨f,hf.entries⟩) hf.entries]; exact ⟨hf,hv'⟩
  let V := Wings.menu (u:=u) (r:=t) S; have hw s : Weighed V (V^s):= Weighed.power V (Wings.sh S) _
  refine ⟨h.fresh,⟨_,(Weighed.constant V hA).times (hw p),fun i=>?_⟩,⟨_,(Weighed.constant V hB).times (hw q),fun i=>?_⟩⟩
  · rw [Pi.mul_apply,Pi.pow_apply,Pi.one_apply,mul_one]; exact (ht i).1.bound
  rw [Pi.mul_apply,Pi.pow_apply]; exact (ht i).2 i.N i.cut
end YM.RG08
