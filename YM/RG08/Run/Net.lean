import YM.RG08.Run.Slacks
/-!
# Unchanged repeated rank on smooth root/fixed address budget. No loss of moment on any D
call. Applied when no exponential costs on that sector after profile integration.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door
open scoped BigOperators Topology Real ContDiff Classical
variable {G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{L:Side}{R σ θ η w A B C:ℝ}
variable {b:Site L}{Q:Cross L (Loc G 1) (Loc G 1)}{V:EnvelopeU D R G r}
local notation "B₁" => Beads (Loc G 1) r
local notation "▵" => Vale.height
section
variable (he:Odd L.val)(hp:1/2≤R)(hx:d+1≤D) (b:Site L)(Q:Cross L (Loc G 1) (Loc G 1))(V:EnvelopeU D R G r)
abbrev Wtr (r d:ℕ) := Fin (d+1+1) × (Fin r → Fin (d+1))
def cheery (r d:ℕ) := univ.filter (fun i:Wtr r d=> burden i.1 i.2 ≤ d)
def tardy (a:B₁ × B₁) := sires (fun i=> readdress (V i) b) (bulb (fun _:Fin r=>node b Q)) a
def morningP (a:B₁ × B₁) := tardy b Q V a-∑ i∈ cheery r d,Vale.whirl he hp hx b Q V i.1 i.2 a
lemma salutation : morningP he hp hx b Q V= ∑ i∈ univ \ cheery r d, Vale.whirl he hp hx b Q V i.1 i.2 := by
  funext a; rw [Finset.sum_apply]; unfold morningP tardy; rw [whirling he hp hx,← Fintype.sum_prod_type (f:=fun i:Wtr r d=>Vale.whirl he hp hx b Q V i.1 i.2 a), sum_sdiff_eq_sub (subset_univ ..)] -- sdiff
set_option maxHeartbeats 600000 in
lemma anthem (hV:Polished V)(hZ:Abates V (d+1))(hv: TakesP Q (rug k) (rug k) d A)(hA:1≤A) (z:B₁): halo b V Q z= ∑' j,morningP he hp hx b Q V (j,z) := by
  obtain ⟨C,hC,H⟩:= whirl_cost (G:=G) (F:=rug k) hp hA (rug_one (α:=Loc G 1) (u:=k)) hx r
  have hx'(x : Wtr r d) := H L Q he hv b V _ (hV k).choose_spec x.1 x.2
  have hv'(x: Wtr r d) : Pens (Vale.whirl he hp hx b Q V x.1 x.2):=Ink.pens (hx' x) (fun i=>fineBro (rug_one (α:= Loc G 1)) _)
  have hh (x:Wtr r d): Summable (fun j=> Vale.whirl he hp hx b Q V x.1 x.2 (j,z)):= (hv' x).of_norm.prod_symm.prod_factor z
  have hm (x: Wtr r d)(hp':x∈cheery r d) : Vale.vanish he hp hx b Q V x.1 x.2=0:= whirled he hp hx hZ hV _ _ _ _ (mem_filter.mp hp'|>.2) (hv' x)
  rw [whirl_pen he hp hx (fun i j=> hv' ⟨i,j⟩),← Fintype.sum_prod_type (f:=fun i:Wtr r d=> Vale.vanish he hp hx b Q V i.1 i.2), salutation,Finset.sum_apply]; simp_rw [Finset.sum_apply]
  rw [Summable.tsum_finsetSum (fun i _=>hh i)]; symm; refine Finset.sum_subset (subset_univ (univ \ cheery r d)) (f:=fun x=>Vale.vanish he hp hx b Q V x.1 x.2 z) ?_
  intro x hX hx; rw [hm x]; rfl; simpa using hx
end

lemma ruby (he:d+1≤k)(z:B₁) :
   (∀ r:ℕ,d+1≤r → girth z<L.val → ▵ L r * tailP r 1 z≤ ▵ L (d+1)*tailP k 1 z) ∧ (∀ r:ℕ,r<d+1 → L.val≤girth z → ▵ L r*tailP r 1 z≤ ▵ L (d+1)*tailP k 1 z) := by
   have ht : ▵ L (d+1)*tailP (d+1) 1 z≤ ▵ L (d+1)*tailP k 1 z := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp) he) (height_p ..).le -- positivity goal
   let M:=(L.val:ℝ); let a := (1+1*(girth z:ℝ))/M; have hp:0<M:= by unfold M; positivity
   have hu : 0≤a:= by unfold a; positivity
   have h i: ▵ L i * tailP i 1 z=a^i:= by unfold a Vale.height tailP M; rw [←mul_pow,div_eq_mul_inv,mul_comm (↑(L.val):ℝ)⁻¹]
   refine ⟨fun r hx hr=> le_trans ?_ ht,fun r hx hr=> le_trans ?_ ht⟩
   · rw [h,h]; apply pow_le_pow_of_le_one hu _ hx; apply (div_le_one hp).2; rw [one_mul]; unfold M; exact_mod_cast (show 1+girth z≤L.val from by omega)
   rw [h,h]; apply pow_le_pow_right₀ _ hx.le; apply (one_le_div hp).2; rw [one_mul]; unfold M; exact_mod_cast (show L.val≤1+girth z from by omega)

private lemma accolade (hd:d+1≤k)(hp:1/2≤R)(hD:d+1≤D) (hw:0<σ)(hb:0≤A)(r:ℕ): ∃ C:ℝ,0≤C ∧ ∀ (L:Side)(b:Site L)(Q:Cross L (Loc G 1) (Loc G 1)),(he:PaysPath Q σ A d)→∀ V:EnvelopeU D R G r, ∀ (z:Beads (Loc G 1) r),cis k 1 (fun i=> morningP he.odd hp hD b Q V (z,i)) (C*(▵ L (d+1)*(tailP k 1 z))*‖V z‖) := by
  obtain ⟨C,hC,H⟩:= far_lug (G:=G) _ r _ hd hp hw hb D
  obtain ⟨B,hB,hP⟩:= growthP σ A hw hb k d (α:=Loc G 1) (β:=Loc G 1) (Nat.le_trans (Nat.le_succ _) hd)
  choose A ha hf using fun j : Wtr r d => trim_ear (G:=G) j.1 j.2 hp hB hD k
  let V:=∑ i,A i; have hx i:0≤A i:= zero_le_one.trans (ha i); have hv:0≤V:=sum_nonneg fun i _=> hx _; let T:=V+C
  have hT:0≤T:=add_nonneg hv hC
  refine ⟨_,hT,fun L b Q he U z=>?_⟩
  let Wh x i:= Vale.whirl he.odd hp hD b Q U (x:Wtr r d).1 x.2 (z,i)
  let p:=univ \ cheery r d
  let a := ▵ L (d+1) * tailP k 1 z; have hN: 0≤tailP k (r:=r) (α:=Loc G 1) 1:=fun i=> (tailp zero_le_one i).trans' zero_le_one
  have he': 0≤a:= mul_nonneg (height_p ..).le (hN z)
  have hy (s:Finset (Wtr r d))(hp:∀ i∈s, cis k 1 (Wh i) (A i*a*‖U z‖)) : cis k 1 (fun j=>∑ i∈s,Wh i j) (V*a*‖U z‖) := by
    rw [show (fun j=>∑ i∈s,Wh i j)=∑ i∈s,Wh i from funext fun _=>(Finset.sum_apply ..).symm]; apply Ink.raise (Ink.additions hp hN); rw [← sum_mul,←sum_mul]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>hx _)) he') (norm_nonneg _)
  by_cases h:girth z<L.val
  · rw [show (fun i=> morningP _ _ _ b Q U (z,i))=(fun j=>∑ x∈p,Wh x j) from funext fun i=>by rw [salutation]; exact Finset.sum_apply ..]
    apply Ink.raise (hy _ ?_); swap
    · intro i hi; apply Ink.raise (hf i L b Q he.odd (hP L Q he) U z (Or.inr h)); exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_trans ((ruby hd z).1 _ (by have hh := (mem_sdiff.mp hi).2; simp only [cheery, mem_filter,mem_univ,true_and] at hh; omega) h) le_rfl) (hx _)) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC) he') (norm_nonneg _)
  let M := fun i=>tardy b Q U (z,i); have hm: cis k 1 M (C*a*‖U z‖):= H L b Q he U z (by omega)
  apply Ink.raise (Ink.less hm (hy (cheery r d) ?_) hN); swap
  · intro i hi; have hv:= (mem_filter.mp hi).2; refine Ink.raise (hf i L b Q he.odd (hP _ _ he) U z (Or.inl hv)) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((ruby hd z).2 _ (Nat.lt_succ_of_le hv) (by omega)) (hx i)) (norm_nonneg _))
  change _ ≤ T*a*_; unfold T; linarith

lemma awarded (hd:d+1≤k)(hp:1/2≤R)(hD:d+1≤D)(hw:0<σ)(h:0≤A)(r:ℕ): ∃ C:ℝ,0≤C ∧ ∀ (L:Side)(b:Site L)(Q:Cross L (Loc G 1) (Loc G 1)),PaysPath Q σ A d →∀ V:EnvelopeU D R G r, Polished V→ Abates V (d+1)→∀ B,cis k 1 V B→cis k 1 (halo b V Q) (C*▵ L (d+1)* B) := by
  obtain ⟨B,hB,H⟩:= accolade (G:=G) hd hp hD hw h r
  obtain ⟨C,hC,hQ⟩:= growthP (α:=Loc G 1) (β:=Loc G 1) σ _ hw h k d (show d≤ k by omega)
  refine ⟨B,hB,fun L b Q hy V hV ht A he=>?_⟩
  let U:= morningP hy.odd hp hD b Q V; rw [funext (anthem hy.odd hp hD b Q V hV ht (hQ L Q hy) hC)]; refine budget_projection (g:=U) _ (fun i=> (zero_lt_one.trans_le (tailp zero_le_one i))) ?_
  have hx i:=H _ b Q hy V i; apply budget_rows (fun i=> tailP k 1 i.2 * ‖U i‖) (fun i=> (B*▵ L (d+1))*(tailP k 1 i*‖V i‖)) _ (budget_scale (mul_nonneg hB (height_p ..).le) he)
  exact fun i=> budget_loosen (hx i) (le_of_eq (by ring))
lemma pan (hd:d+1≤k)(hp:1/2≤R)(hD:d+1≤D)(hw:0<σ)(h:0≤A)(r:ℕ): ∃ C:ℝ,0≤C ∧ ∀ (L:Side)(Q:Cross L (Loc G 1) (Loc G 1)),PaysPath Q σ A d→∀ V:EnvelopeU D R G r,Polished V→ Abates V (d+1)→∀ B,cis k 1 V B→cis k 1 (aboard d Q V) (C / L.val*B) := by
  obtain ⟨C,hC,H⟩:= awarded (G:=G) hd hp hD hw h r; refine ⟨C,hC,fun L Q hQ V hz hv B hp=>?_⟩
  apply Ink.raise (Ink.scale (Ink.additions (s:=univ) (f:=fun b:Site L=> halo b V Q) (fun i _=> H L i Q hQ V hz hv B hp) (zero_le_one.trans (tailp zero_le_one))) _); rw [sum_const,card_univ,nsmul_eq_mul,Real.norm_of_nonneg (by positivity)]; apply le_of_eq; unfold Vale.height; rw [inv_pow,pow_succ]; field_simp
end YM.RG08.Run
