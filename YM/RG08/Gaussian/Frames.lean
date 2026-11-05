import YM.RG08.Gaussian.Menus

/-!
# Repeated frame supplies for the gauge-to-tree projection

All equality on translated, wrapped, genuine coordinates. In particular
patch paths crossing block or period boundaries don't get dropped. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Finset Laurent Lattice Wilson RG Precision Exterior Bloch Matrix
open Next.Free Work.F08 Tree Stationary FreeResolvent
open scoped Topology BigOperators Classical

section scaffold
variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
lemma menu_ink (A : Matrix α β ℝ) (u : γ→ℝ) (f : δ) (p : α ≃ δ) (q : β ≃ γ) :
    (repackM p q A *ᵥ u) f=(A*ᵥ (u∘q)) (p.symm f) := by
  have h := repack_act p q A (u∘q)
  simp only [comp_def,q.apply_symm_apply] at h
  exact congr_fun h _
end scaffold

section
variable (G : Gauge) (P : Patch) (K : KernelChoices)

abbrev linked (P : Patch) (K : KernelChoices) (c f : Side) (h : f.val = c.val*P.L.val) : StepData c f := ⟨P,K,h⟩

-- construct view in terms of linear functional evaluated separately. even color index-free.
variable {G P K}
def safari (G : Gauge) (P : Patch) (K : KernelChoices) (u : Cover) (d : Walk) (j : G.ColorIndex) : View P.L (Co P.L (Loc G 1)) :=
    fun c f h v z =>
      let S := linked P K c f h
      integralLink (wrap f u + S.ratio.embed z) d (component (v ∘ unitSplit G S 1) j)

lemma near_edge (G : Gauge) (P : Patch) (K : KernelChoices) (j : Loc G 1) (u : Cover) :
    Menu (L:=P.L) (α:=Co P.L (Loc G 1)) (fun c f h v z =>
      let S := linked P K c f h; v (unitSplit G S 1 (wrap f u + S.ratio.embed z,j))) := by
  refine (Menu.single P.L ((wrap P.L u, j):Co P.L (Loc G 1)) (rent P.L u)).relabel ?_
  intro c f h v z; let S := linked P K c f h
  dsimp only
  rw [show wrap f u+(linked P K c f h).ratio.embed z=S.ratio.assemble _ from sewn S u z,unitSplit,split_co]
  change v _=v (S.ratio.parent _,S.ratio.residue _,j)
  rw [S.ratio.assemble_parent,S.ratio.assemble_res, add_comm z]
lemma near_path (P : Patch) (K : KernelChoices) (u : Cover) (j : G.ColorIndex) (d : Walk) :
    Menu (safari G P K u d j) := by
  induction d generalizing u with
  | nil => exact Menu.zero P.L _
  | cons a l IH =>
    let p (c f : Side) (h : f.val=c.val*P.L.val) (z : Site c) := wrap f u+(linked P K c f h).ratio.embed z
    let v := a.used u
    rcases a with ⟨i,B⟩; cases B
    · apply Menu.relabel ((near_edge G P K (coord i,j) u).add (IH (u+step i)))
      intro c f h x z; unfold safari
      simp only [map_add,wrap_step, add_right_comm (wrap f u) (step i)]; rfl
    apply Menu.relabel ((IH (u-step i)).sub (near_edge G P K (coord i,j) (u-step i)))
    intro c f h x z
    unfold safari; dsimp only
    rw [map_sub,wrap_step]
    let S:=linked P K c f h; let a:=p c f h z
    rw [show wrap f u-step i+S.ratio.embed z=a-step i by unfold a p S; abel]
    change linkSum _ _ _ - x _ = linkSum _ a _
    rw [linkSum]; change _ - _ = - (x _) + linkSum _ (a + -step i) _; rw [← sub_eq_add_neg, sub_eq_add_neg (G:=ℝ), add_comm (_ : ℝ)]; rfl
end

section
variable (G : Gauge) (P : Patch) (K : KernelChoices) (X : Repeated P.L)

abbrev hikeOffer : Offers P.L (Co P.L (Loc G 0)) (Co P.L (Loc G 1)) :=
    fun c f h => let S := linked P K c f h
                 repackM (unitSplit G S 0) (unitSplit G S 1) (hikeM S G (X.forest S.ratio))
abbrev rootOffer : Offers P.L (Loc G 0) (Co P.L (Loc G 1)) :=
    fun c f h => let S := linked P K c f h
                 repackM (Equiv.refl _) (unitSplit G S 1) (stampZone S G)
abbrev meanOffer : Offers P.L (Loc G 1) (Co P.L (Loc G 1)) :=
    fun c f h => let S := linked P K c f h
                 repackM (Equiv.refl _) (unitSplit G S 1) (bondsM G S)
abbrev frameOffer : Offers P.L (Loc G 1) (Co P.L (Loc G 1)) :=
    fun c f h => let S := linked P K c f h
                 repackM (Equiv.refl _) (unitSplit G S 1) (patron G (probe S))
abbrev dupOffer : Offers P.L (Co P.L (Loc G 0)) (Loc G 0) :=
    fun c f h => let S := linked P K c f h
                 repackM (unitSplit G S 0) (Equiv.refl _) (duplicateM S G)
abbrev bodyOffer : Offers P.L (Co P.L (Loc G 1)) (ParcelG G P.L) :=
    fun c f h => let S := linked P K c f h
                 repackM (unitSplit G S 1) (clothe G S) (butt G c f)
abbrev edgeOffer : Offers P.L (Loc G 0) (ParcelG G P.L) :=
    fun c f h => let S := linked P K c f h
                 repackM (Equiv.refl _) (clothe G S) (brim G c f)

lemma nest {c f : Side} (S : StepData c f) (z : Site c) (i : Site S.patch.L) :
    let y := wrap f (lift i)+S.ratio.embed z
    S.ratio.parent y=z ∧ S.ratio.residue y=i := by
  intro y
  have h : y=S.ratio.assemble (z,i) := add_comm ..
  rw [h]
  exact ⟨S.ratio.assemble_parent _, S.ratio.assemble_res _⟩

variable {P}
lemma hike_offer (σ : ℝ) (hσ : 0<σ) : Repeats (hikeOffer G P K X) σ := by
  refine menu_repeats hσ ?_
  intro i
  obtain ⟨u,a,j⟩ := i; rw [vac_only a]
  refine (near_path P K (lift u) j (X.path u)).relabel ?_
  intro c f h v z
  unfold safari hikeOffer; dsimp only; let S := linked P K c f h
  let b := (z,(u,(vac,j)))
  let y := wrap f (lift u)+S.ratio.embed z
  have he := nest S z u
  have hx : unitSplit G S 0 (y,vac,j)=b := by unfold unitSplit; rw [split_co,he.1,he.2]; rfl
  change integralLink y _ _=(repackM (unitSplit G S 0) (unitSplit G S 1) (hikeM S G (X.forest S.ratio)) *ᵥ v) b
  rw [menu_ink, show (unitSplit G S 0).symm b=(y,vac,j) from (Equiv.symm_apply_eq ..).mpr hx.symm,hikeM_pay]
  unfold potential; simp only [Repeated.branches,show S.ratio.residue y=u from he.2]; rfl
variable (P)
lemma dup_offer (σ : ℝ) (hσ : 0<σ) : Repeats (dupOffer G P K) σ := by
  refine menu_repeats hσ ?_
  rintro ⟨i,a⟩; refine (Menu.single P.L a 0).relabel ?_
  intro c f h v z; let S:=linked P K c f h; let b:=(z,i,a)
  let y := wrap f (lift i)+S.ratio.embed z
  have he := nest S z i
  have hx : unitSplit G S 0 (y,a)=b := by unfold unitSplit; rw [split_co,he.1,he.2]; rfl
  change v _=(repackM (unitSplit G S 0) (Equiv.refl _) (duplicateM S G)*ᵥ v) b
  rw [menu_ink,show (unitSplit G S 0).symm b=(y,a) from (Equiv.symm_apply_eq ..).mpr hx.symm,duplicate_reads]
  change v _=v (_,_); rw [show S.ratio.parent y=z from he.1,map_zero,add_zero]

lemma body_offer (σ : ℝ) (hσ : 0<σ) : Repeats (bodyOffer G P K) σ := by
  refine menu_repeats hσ ?_
  intro b
  refine (Menu.single P.L (Sum.inl b : ParcelG G P.L) 0).relabel ?_
  intro c f h v z; let S:=linked P K c f h
  change v _=(repackM _ _ (butt G c f)*ᵥ v) _
  rw [menu_ink,helmet_butt,sliceX]
  change v _=v (clothe G S (Sum.inl ((unitSplit G S 1).symm (z,b))))
  rw [inflowL, Equiv.apply_symm_apply,map_zero,add_zero]; rfl
lemma edge_offer (σ : ℝ) (hσ : 0<σ) : Repeats (edgeOffer G P K) σ := by
  refine menu_repeats hσ ?_
  intro b; refine (Menu.single P.L (Sum.inr b : ParcelG G P.L) 0).relabel ?_
  intro c f h v z
  change v _=(repackM _ _ (brim G c f)*ᵥ v) _
  rw [menu_ink,helmet_brim,sliceY]; change v (_,_) = v (z,.inr b)
  rw [map_zero,add_zero]

lemma mean_offer (σ : ℝ) (hσ : 0<σ) : Repeats (meanOffer G P K) σ := by
  refine menu_repeats hσ ?_
  rintro ⟨a,j⟩
  let d := List.replicate P.L.val (posDir (axisEquiv.symm a))
  let f (i : P.Points) : View P.L (Co P.L (Loc G 1)) :=
    fun c n h v z => P.weight i * safari G P K i.val d j c n h v z
  refine (Menu.total univ f fun i _ => (near_path P K i.val j d).scale _).relabel ?_
  intro c n h v z; let S := linked P K c n h
  change (∑ i : P.Points, _)= (repackM _ _ _ *ᵥ v) (z,a,j)
  erw [menu_ink]; dsimp only [meanOffer,Equiv.refl_apply,Equiv.refl_symm]
  let w:=v ∘ unitSplit G S 1
  change _=(bondsM G S*ᵥ w) (z,a,j)
  rw [bondsM,tensor_same]
  change _=component (tensor G (mean S) *ᵥ w) j (z,a)
  rw [component_mul, mean,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,LinearMap.sum_apply]
  rfl

def tauM (i : P.Points) (j : G.ColorIndex) : View P.L (Co P.L (Loc G 1)) := fun c n h v z =>
    let S := linked P K c n h
    tau S z i (component (v ∘ unitSplit G S 1) j)
lemma tau_menu (i : P.Points) (j : G.ColorIndex) : Menu (tauM G P K i j) := by
  let p := -((Fintype.card P.Points:ℝ)⁻¹); let q := (Fintype.card Lattice.Order:ℝ)⁻¹
  let A (b : P.Points) : View P.L (Co P.L (Loc G 1)) := fun c n h v z => q*∑ d : Lattice.Order,
    safari G P K i.val (route i.val b.val d) j c n h v z
  have hA b : Menu (A b) := (Menu.total univ _ (fun d _ => near_path P K i.val j (route i.val (b:P.Points).val d))).scale q
  refine ((Menu.total univ A (fun b _ => hA b)).scale p).relabel ?_
  intro c n h v z; let S := linked P K c n h
  change p*_=tau S z i (component (v ∘ unitSplit G S 1) j)
  simp only [p,tau,LinearMap.neg_apply, LinearMap.smul_apply,LinearMap.sum_apply,smul_eq_mul, neg_mul]
  rfl

lemma root_offer (σ : ℝ) (hσ : 0<σ) : Repeats (rootOffer G P K) σ := by
  refine menu_repeats hσ ?_
  rintro ⟨i,j⟩
  let f (b : P.Points) : View P.L (Co P.L (Loc G 1)) := fun c n h v z => P.weight b*tauM G P K b j c n h v z
  refine ((tau_menu G P K P.center j).sub (Menu.total univ f (fun b _ => (tau_menu G P K b j).scale _))).relabel ?_
  intro c n h v z; let S := linked P K c n h
  unfold rootOffer; dsimp only
  erw [menu_ink]; let w := v ∘ unitSplit G S 1
  change _ = component (tensor G (fixRoot S) *ᵥ w) j (z,i)
  rw [component_mul,fixRoot,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,adjusted, LinearMap.sub_apply, LinearMap.sum_apply]
  rfl

lemma frame_offer (σ : ℝ) (hσ : 0<σ) : Repeats (frameOffer G P K) σ := by
  let M : Offers P.L (Loc G 1) (Loc G 0) := fun c _ _ => tensor G (d 0 c)
  obtain ⟨C,-,H⟩ := delta_budget 0 σ
  have hX : Repeats M σ := repeater ⟨colored G (cobound 0),C,colored_price G H,fun _ _ _ => colored_acts ..⟩
  apply Repeats.repl ((mean_offer G P K σ hσ).plus (hX.mult (root_offer G P K σ hσ) hσ.le) hσ)
  intro c f h; let S := linked P K c f h
  change _=repackM (Equiv.refl _) (unitSplit G S 1) (patron G (probe S))
  rw [base_test,show repackM (Equiv.refl _) (unitSplit G S 1) (bondsM G S + _) =
      repackM (Equiv.refl _) (unitSplit G S 1) (bondsM G S) + repackM (Equiv.refl _) (unitSplit G S 1)
      (tensor G (d 0 c)*tensor G (fixRoot S)) from rfl, repack_multiply _ (Equiv.refl _)]
  rfl
end
end YM.RG08
