import YM.RG08.Vale.Mom
/-!
# Tensor formula for the radial leading mark ports
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire
open scoped Topology ContDiff Classical BigOperators
variable {α E : Type} {j k r u : ℕ} {m : Side} {C A : ℝ}
variable {V : Shale α r}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
def LeafPath (E : Type) (α : Type) := (Cover×α) → E → ℝ
def penny (V : Shale α r) (X : LeafPath E α) (x : Fin j → E) (c : OrderedFinpartition j) : ℝ :=
    (c.length.factorial:ℝ)* wallet (grant c.length V) (fun i z=> iteratedFDeriv ℝ (c.partSize i) (X z) 0 (x ∘ c.emb i))
def vault (V : Shale α r) (X : LeafPath E α) (x : Fin j → E) := ∑ c, penny V X x c
lemma grant_else (h : k≠r) (V : Shale α r): grant k V=0 := by simp [grant,h]
lemma polish_grant (h:Polished V) (n): Polished (grant n V) := by
  by_cases hx:n=r; subst n; rwa [grant_self]; rw [grant_else hx]; exact polished_zero ℝ _ _
lemma grant_price (h: Ink (mint u) V C) (n) : Ink (mint u) (grant n V) C := by
  by_cases hz:n=r; subst n; rwa [grant_self]; rw [grant_else hz]; exact (Ink.none ..).raise h.nonneg
@[simp] lemma wallet_zero (f : Fin r→Cover×α→ℝ) : wallet (0:Shale α r) f=0 := by simp [wallet]
variable {P F : LeafPath E α}
variable [Fintype α]
def Plenty (P : LeafPath E α) (m : ℕ→Side) (S : (p:ℕ)→E→PAC α (m p)) : Prop :=
    ∀ k (x : Fin k → E), (∀ u:Cover×α, Tendsto (fun p=> iteratedFDeriv ℝ k (S p) 0 x (wrap (m p) u.1,u.2)) atTop (𝓝 (iteratedFDeriv ℝ k (P u) 0 x))) ∧
    ∃ (n:ℕ) (C:ℝ),0≤C ∧ ∀ u:Cover×α,∀ p,‖iteratedFDeriv ℝ k (S p) 0 x (wrap (m p) u.1,u.2)‖ ≤ C*dime n u.1
lemma plenish {m:ℕ→Side} {S:(p:ℕ)→E→PAC α (m p)} (hm:Tendsto (fun i=>(m i).val) atTop atTop) (hV : Tidy V) (h : Polished V)
    (hp : Plenty P m S)(ht:∀ i,ContDiffAt ℝ ω (S i) 0)(hx : ∀ i,S i 0=0)(x : Fin j→E):
    Tendsto (fun i=> iteratedFDeriv ℝ j (rootSong V (m i) 0 ∘ S i) 0 x) atTop (𝓝 (vault V P x)) := by
  have hu (i j:ℕ)(z:Site (m i)) : iteratedFDeriv ℝ j (rootSong V _ z) 0=(j.factorial:ℝ) • stitch (grant j V) _ z := by
    let n := (j.factorial:ℝ); have he: n≠0 := by unfold n; positivity
    have hz : Tensor.coeff (rootSong V _ z) j 0= stitch (grant j V) _ z := by
      by_cases hb:j=r
      · subst j; rw [grant_self]; exact coeff_at_diagonal _ (hV.sym z)
      rw [grant_else hb,st_zero]; exact coeff_diagonal_else _ (hV.sym z) hb
    conv_rhs => rw [←hz,Tensor.coeff]; rw [smul_inv_smul₀ he]
  have he i c : Cases.caseRead c (rootSong V (m i) 0) (S i) 0 x=
        (c.length.factorial:ℝ)* stitch (grant c.length V) (m i) 0 (fun j=> iteratedFDeriv ℝ _ (S i) 0 (x∘c.emb j)) := by unfold Cases.caseRead; rw [hx,hu,_root_.smul_apply]; rfl
  have hg i : ContDiffAt ℝ ω (rootSong V _ (0:Site (m i))) (S i 0) := (Tensor.diag_smooth ..).contDiffAt
  simp_rw [Cases.compReads (hg _) (ht _) le_top x,he]
  apply tendsto_finsetSum _; intro b _
  let g (i : Fin b.length) z := iteratedFDeriv ℝ _ (P z) 0 (x ∘ b.emb i)
  let t (i:ℕ)(k:Fin b.length) := iteratedFDeriv ℝ _ (S i) 0 (x∘b.emb k)
  choose n D hd hu' using fun i : Fin b.length=> (hp _ (x ∘ b.emb i)).2
  let N:=∑ i,n i
  refine tendsto_const_nhds.mul (wallet_limit hm (polish_grant h _) (v:=t) (fun j k=> (hp _ _).1 _) N (fun i=> hd i) ?_)
  intro i p a j; exact (hu' i (p,a) j).trans (mul_le_mul_of_nonneg_left (dime_more (single_le_sum (fun i _=>Nat.zero_le (n i)) (mem_univ i)) _) (hd i))

omit [Fintype α] in
lemma receipt (P:LeafPath E α) (j r u : ℕ)
    (h : ∀ n ≤ j,∃ C:ℝ,0≤C ∧ ∀ x, ‖iteratedFDeriv ℝ n (P x) 0‖ ≤ C*dime u x.1) :
    ∃ C:ℝ,0≤C ∧ ∀ x : Fin j→E,∀ (H:Shale α r) (D:ℝ), Ink (mint u) H D→ ‖vault H P x‖ ≤ (C*D)*∏ i, ‖x i‖ := by
  have he (c:OrderedFinpartition j) (i : Fin c.length) : c.partSize i≤j := by
    simpa using Fintype.card_le_of_injective (c.emb i) (c.emb_strictMono i).injective
  choose A hA hL using fun (c:OrderedFinpartition j) i=>h _ (he c i)
  let C (c:OrderedFinpartition j):=(c.length.factorial:ℝ)*∏ i,A c i
  refine ⟨∑ i,C i,Finset.sum_nonneg fun i _=> mul_nonneg (by positivity) (prod_nonneg fun j _=> hA i j),fun x H D hz=>?_⟩
  rw [sum_mul,sum_mul]; apply (norm_sum_le ..).trans (sum_le_sum _); intro b _; unfold penny
  let f (i : Fin b.length) := ∏ j, ‖(x ∘ b.emb i) j‖
  have hf i : 0≤f i:= by unfold f; positivity
  have ht (a:Cover×α)(i:Fin b.length) : ‖iteratedFDeriv ℝ _ (P a) 0 (x ∘ b.emb i)‖≤(A b i*f i)*dime u a.1 := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ _ (P a) 0‖*f i:= (iteratedFDeriv ℝ (b.partSize i) (P a) 0).le_opNorm (x ∘ b.emb i)
      _ ≤ (A b i*dime u a.1)*f i := mul_le_mul_of_nonneg_right (hL b i a) (hf i)
      _ = _ := mul_right_comm ..
  rw [norm_mul,Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (b.length.factorial:ℝ)*((∏ i,(A b i*f i))*D):= mul_le_mul_of_nonneg_left (wallet_cost (grant_price hz b.length) (C:=fun i=> A b i*f i) (fun i=> mul_nonneg (hA b i) (hf i)) (fun k a=> ht a k)) (by positivity)
    _ = _ := by rw [prod_mul_distrib,show (∏ i,f i)=_ from b.prod_sigma_eq_prod (fun i=>‖x i‖)]; unfold C; ring

lemma piles {m:ℕ→Side} {S:(p:ℕ)→E→PAC α (m p)} (hm:Tendsto (fun i=>(m i).val) atTop atTop) (hV:Tidy V) (h : Polished V)
    (hp : Plenty P m S)(ht:∀ i,ContDiffAt ℝ ω (S i) 0)(hx : ∀ i,S i 0=0)(j : ℕ) {C:ℝ} (he : ∀ x:Fin j→E, ‖vault V P x‖≤C*∏ i,‖x i‖):
    ∃ M : Tensor.T E ℝ j, Tensor.Sym M ∧ ∀ x,M x=vault V P x := by
  let T i := iteratedFDeriv ℝ j (rootSong V _ (0:Site (m i)) ∘ S i) 0
  have H v:= show Tendsto (fun i=> T i v) atTop (𝓝 (vault V P v)) from plenish hm hV h hp ht hx v
  let A : MultilinearMap ℝ (fun _:Fin j=>E) ℝ := {
    toFun := vault V P
    map_update_add' x i y z := tendsto_nhds_unique (H _) (Tendsto.congr' (Eventually.of_forall fun n=> Eq.symm ((T n).map_update_add _ _ _ _)) ((H _).add (H _)))
    map_update_smul' x i y z := tendsto_nhds_unique (H _) (Tendsto.congr' (Eventually.of_forall fun n=> Eq.symm ((T n).map_update_smul _ _ _ _)) (tendsto_const_nhds.smul (H _))) }
  refine ⟨{ toMultilinearMap:=A, cont:=A.continuous_of_bound C he }, fun x t=>?_,fun _=>rfl⟩
  have hi i : Tensor.Sym (T i) := by
    let F:=rootSong V _ (0:Site (m i)) ∘ S i
    have he:= Tensor.coeff_symm (show ContDiffAt ℝ j F 0 from (((Tensor.diag_smooth ..).contDiffAt).comp _ (ht i)).of_le le_top)
    intro x t; exact smul_right_injective ℝ (show ((j.factorial:ℝ)⁻¹)≠0 by positivity) (he x t)
  exact tendsto_nhds_unique_of_eventuallyEq (H _) (H _) (.of_forall fun i=> hi i x t)
end YM.RG08.Vale
