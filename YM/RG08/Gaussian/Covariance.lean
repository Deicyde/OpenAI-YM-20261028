import YM.RG08.Gaussian.Frames

/-!
# Flat coefficient recipe: full conditional covariance on the cover
Includes harmonic and zero modes. Real counts, not the orbifold projection.
Uniform over history of finer blocking. Equalities holding on every period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice Wilson RG Precision Exterior Bloch Matrix
open Next.Free Work.F08 Tree Stationary FreeResolvent
open scoped Topology BigOperators Classical

variable (G : Gauge) {P : Patch} (X : Repeated P.L) (k : KernelChoices)

abbrev tourOffer : Offers P.L (Co P.L (Loc G 0)) (ParcelG G P.L) :=
    fun c f h => let S:= linked P k c f h
                 repackM (unitSplit G S 0) (clothe G S) (turnParameter S (X.forest S.ratio) G)
abbrev projectionOffer : Offers P.L (Co P.L (Loc G 1)) (ParcelG G P.L) :=
    fun c f h => let S:= linked P k c f h
                 repackM (unitSplit G S 1) (clothe G S) (projection S (X.forest S.ratio) G)

lemma tour_offer (σ : ℝ) (hp : 0<σ) : Repeats (tourOffer G X k) σ := by
  have ha := body_offer G P k σ hp
  have hA := (root_offer G P k σ hp).mult ha hp.le
  have hg := ((dup_offer G P k σ hp).mult ((edge_offer G P k σ hp).plus hA hp) hp.le).minus
      ((hike_offer G k X σ hp).mult ha hp.le) hp.le
  apply hg.repl
  intro c f h; let S:=linked P k c f h
  let H := X.forest S.ratio
  change _ = repackM (unitSplit G S 0) (clothe G S) (turnParameter S H G)
  unfold turnParameter
  let M := duplicateM S G * (brim G c f+stampZone S G * butt G c f)
  change _ = repackM (unitSplit G S 0) (clothe G S) M -
      repackM (unitSplit G S 0) (clothe G S) (hikeM S G H * butt G c f)
  unfold M
  rw [repack_multiply _ (Equiv.refl _),repack_multiply (V:=butt G c f) _ (unitSplit G S 1)]
  rw [show repackM (Equiv.refl _) (clothe G S) (brim G c f+stampZone S G * butt G c f)=
      repackM (Equiv.refl _) (clothe G S) (brim G c f)+repackM (Equiv.refl _) (clothe G S) (stampZone S G * butt G c f) from rfl,
      repack_multiply _ (unitSplit G S 1)]
  rfl

lemma projection_offer (σ : ℝ) (hp : 0<σ) : Repeats (projectionOffer G X k) σ := by
  let M : Offers P.L (Co P.L (Loc G 1)) (Co P.L (Loc G 0)) :=
    fun c f h => let S:= linked P k c f h
                 repackM (unitSplit G S 1) (unitSplit G S 0) (tensor G (d 0 f))
  obtain ⟨C,-,h⟩ := delta_budget 0 σ
  have hu := colored_price G h
  have hM : Repeats M σ := repeater ⟨_, _, native_price (L:=P.L) hu hp.le
        (le_mul_of_one_le_left hp.le (by exact_mod_cast P.L.property)), ?_⟩
  swap
  · intro c f h
    let S:=linked P k c f h
    erw [native_acts S.ratio (colored_whole G (Whole.boundary 0)), colored_acts G]
  refine Repeats.repl ((body_offer G P k σ hp).minus (hM.mult (tour_offer G X k σ hp) hp.le) hp.le) ?_
  intro c f h; let S:=linked P k c f h; let T:=X.forest S.ratio
  change _=repackM (unitSplit G S 1) (clothe G S) (butt G c f)-
      repackM (unitSplit G S 1) (clothe G S) (tensor G (d 0 f)*turnParameter S T G)
  rw [repack_multiply _ (unitSplit G S 0)]
  rfl

lemma portray {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (t : α ≃ β) (U : Matrix α α ℝ) (V : Matrix β β ℝ) (h : repackM t t U * V=1) :
    ∃ L, U*L=1 ∧ V=repackM t t L := by
  let L := repackM t.symm t.symm V
  have he : V=repackM t t L := by ext i j; unfold L; simp [repackM]
  refine ⟨L,?_,he⟩
  rw [he,← repack_multiply] at h
  ext i j
  have ht := congr_fun (congr_fun h (t i)) (t j)
  simpa [repackM, Matrix.one_apply] using ht

/- Canonical `pink` decided for each Train.
   Slice parameter offered in algebra; `Larger` etc not needed even for 
   PosDef (by joint projection). Project with Frame leg accounting. -/
def covOffer (w : Train P.J) : Offers P.L (Co P.L (Loc G 1)) (Co P.L (Loc G 1)) :=
    fun c f h => let S:= linked P k c f h
                 let T := X.forest S.ratio
                 repackM (unitSplit G S 1) (unitSplit G S 1) (FreeResolvent.covariance G S T (pink k.penalty w))

theorem covariance_funding (G : Gauge) (k : KernelChoices) (j : ℕ) (hj : 4 ≤ j) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ P : Patch, P.J=j → P.Branches k G →
      ∀ X : Repeated P.L, ∃ M : ℝ, 0 ≤ M ∧ ∀ w : Train P.J,
        ∃ Q : Row (Co P.L (Loc G 1)) (Co P.L (Loc G 1)), Q.strip σ M ∧ ∀ c f h, Q.acts c=covOffer G X k w c f h := by
  obtain ⟨σ,hσ,H⟩ := joint_universal G k j hj
  refine ⟨σ,hσ,fun P hp hk X => ?_⟩
  obtain ⟨x,hx,A⟩ := H P hp hk
  obtain ⟨C,hC,F,hF,Hf⟩ := projection_offer G X k σ hσ
  let n := (Fintype.card (ParcelG G P.L):ℝ)
  let K := n*(n*(C*x)*C)
  refine ⟨K,by unfold K n; positivity,fun w => ?_⟩
  obtain ⟨Q,hQ,Y⟩ := A w
  let M := pink k.penalty w
  have hJ : 4≤P.J := hp ▸ hj
  have hm : Whole M := (heart_saves _ k.penalty_pos hJ (id : Train P.J → _)).1.whole w
  refine ⟨_,strip_compose hσ.le (strip_compose hσ.le hF hQ) (strip_trans hF),?_⟩
  intro c f h; let S := linked P k c f h
  let t : S.Choices := (fun _ => (P.center,1),fun _ => P.center)
  let V := X.forest S.ratio; let W := clothe G S; let D := unitSplit G S 1
  obtain ⟨N,hN,hv⟩ := portray W _ _ (Y c f h t)
  rw [hessian_acts hm] at hN
  have he := projecting S hk V t ((heart_inverse _ k.penalty_pos hJ w f).2.1) hN
  rw [acts_compose hσ.le (strip_compose hσ.le hF hQ) (strip_trans hF),acts_compose hσ.le hF hQ,
      acts_trans,hv,Hf c f h]
  change repackM D W (projection S V G) * repackM W W N * (repackM D W (projection S V G))ᵀ=_
  change _=repackM D D (FreeResolvent.covariance G S V M)
  rw [← repack_multiply,← repack_rotate,← repack_multiply,he.2]

-- even a non-repeated forest works for finite formal calculation
lemma forest_precision (w : Train P.J) (c f : Side) (h : f.val=c.val*P.L.val)
    (H : P.Branches k G) (T : Forest (linked P k c f h).ratio) :
    PosDef (treeMatrix G (linked P k c f h) T (pink k.penalty w)) := by
  have hj : 4 ≤ P.J := P.order_cut
  let S:= linked P k c f h
  let M:= pink k.penalty w
  let t : S.Choices := (fun _ => (P.center,1),fun _ => P.center)
  obtain ⟨σ,-,K⟩ := joint_universal G k P.J hj
  obtain ⟨u,-,H'⟩ := K P rfl H
  obtain ⟨Y,-,hY⟩ := H' w
  obtain ⟨N,hN,hv⟩ := portray _ _ _ (hY c f h t)
  rw [hessian_acts (show Whole (pink k.penalty w) from (heart_saves k.penalty k.penalty_pos hj (id : Train P.J → _)).1.whole w)] at hN
  let F:= treeMatrix G S T M
  have hx : PosSemidef F := psd_tree S T (origins_psd _ k.penalty_pos hj w f)
  have he := projecting S H T t ((heart_inverse _ k.penalty_pos hj w f).2.1) hN
  change F.PosDef; apply hx.posDef_iff_isUnit.mpr
  exact ⟨⟨_,_,he.1,mul_eq_one_comm.mp he.1⟩,rfl⟩

private lemma cov_seed (G : Gauge) (X : Repeated P.L) (K : KernelChoices) (w : Train P.J) :
    P.Branches K G → ∃ Q : Row (Co P.L (Loc G 1)) (Co P.L (Loc G 1)), Whole Q ∧ ∀ c f h, Q.acts c = covOffer G X K w c f h := by
  intro hB
  obtain ⟨σ,C,H⟩ := covariance_funding G K P.J P.order_cut
  obtain ⟨M,hM,U⟩ := H P rfl hB X
  obtain ⟨R,hR,HP⟩ := U w
  exact ⟨R,⟨_,_,C,hR⟩,HP⟩

/-- Pre-decided *cover* bulk inverse. Genuine periodization with repeated
    forest and price conventions. Set to zero on inadmissible branches. -/
def conditionalCov (G : Gauge) {P : Patch} (X : Repeated P.L) (k : KernelChoices) (w : Train P.J) : Row (Co P.L (Loc G 1)) (Co P.L (Loc G 1)) :=
    if h : P.Branches k G then (cov_seed G X k w h).choose else 0
lemma conditional_truth (w : Train P.J) (hB : P.Branches k G) :
    Whole (conditionalCov G X k w) ∧ ∀ c f h,(conditionalCov G X k w).acts c=covOffer G X k w c f h := by
  rw [conditionalCov,dif_pos hB]; exact (cov_seed G X k w hB).choose_spec

theorem conditional_funds (G : Gauge) (k : KernelChoices) (j : ℕ) (hj : 4 ≤ j) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ P : Patch, P.J=j → P.Branches k G →
      ∀ X : Repeated P.L, ∃ M : ℝ, 0 ≤ M ∧ ∀ w : Train P.J,(conditionalCov G X k w).strip σ M := by
  obtain ⟨σ,hσ,H⟩ := covariance_funding G k j hj
  refine ⟨σ,hσ,fun P hp h X => ?_⟩
  obtain ⟨M,hM,Y⟩ := H P hp h X
  refine ⟨M,hM,fun w => ?_⟩
  obtain ⟨Q,hQ,hU⟩ := Y w
  have hx := conditional_truth G X k w h
  rw [bank_injective hx.1.safe (Whole.safe ⟨_,_,hσ,hQ⟩) (fun c => Eq.trans (hx.2 c (c*P.L) rfl) (hU c (c*P.L) rfl).symm)]
  exact hQ
end YM.RG08
