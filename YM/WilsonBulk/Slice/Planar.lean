import YM.WilsonBulk.Slice.Print

/-!
# Seated chamber map and real receipt toolkit for analytic germs
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical BigOperators ContDiff
open Function Filter Sum Finset Matrix PowerSeries
variable {α β ι κ : Type} [Fintype α] [Fintype β] [Fintype ι] [Fintype κ] {f g : Tabletop α→ℝ} {W : Matrix β α ℝ}
-- real stencil api

def upper (α β : Type) [Fintype α] [Fintype β] : Tabletop (Chamber α β) →L[ℝ]Tabletop α := ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (inl i)
def lower (α β : Type) [Fintype α] [Fintype β] : Tabletop (Chamber α β) →L[ℝ] Tabletop β := ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (inr i)
@[simp] lemma upper_apply (z : Tabletop (Chamber α β)) (i) : upper α β z i=z (inl i):= rfl
@[simp] lemma lower_apply (z : Tabletop (Chamber α β)) (i) : lower α β z i=z (inr i):= rfl
@[simp] lemma upper_both (x : Tabletop α) (y : Tabletop β) : upper α β (Sum.elim x y)=x := rfl
@[simp] lemma lower_both (x : Tabletop α) (y : Tabletop β) : lower α β (Sum.elim x y)=y := rfl
lemma mirror_pose (z : Tabletop (Chamber α β)) : Sum.elim (upper _ _ z) (lower _ _ z)=z := funext fun i=> by cases i <;> rfl
def assemble (α β : Type) [Fintype α] [Fintype β] : (Tabletop α × Tabletop β) ≃L[ℝ] Tabletop (Chamber α β) := LinearEquiv.toContinuousLinearEquiv {
  toFun := fun z=> Sum.elim z.1 z.2
  invFun := fun z=> (upper _ _ z,lower _ _ z)
  left_inv := fun z=> rfl
  right_inv:= mirror_pose
  map_add' u v:= funext fun i=> by cases i <;> rfl
  map_smul' r u:= funext fun i=> by cases i <;> rfl }
lemma assemble_ (x : Tabletop α) (y : Tabletop β): assemble α β (x,y)= Sum.elim x y:= rfl
@[simp] lemma upper_code : exposure (upper α β) = (fun i=> privateName i) := funext flashL where
  flashL (i) := (flash_named (inl i : Chamber α β))
@[simp] lemma lower_code : exposure (lower α β)=(fun i=> viewer i) := funext fun i=> flash_named (Sum.inr i)
def mountain (α β : Type) [Fintype α] [Fintype β] : Tape α →ₐ[ℝ]StageD α β := submit (fun i=>privateName i)
lemma boast_neat : submit (exposure (lower α β)) = boast α β := by rw [lower_code]; rfl
lemma flash_front {g : Tabletop β→ℝ} (hg : ContDiffAt ℝ ω g 0) (h : g 0=0) : flash (g ∘ lower α β)= boast α β (flash g) := by rw [flash_comp hg h (lower α β).contDiff.contDiffAt (map_zero _),boast_neat]
lemma quill_smooth (W : Matrix β α ℝ) : ContDiff ℝ ω (quill W (A:=ℝ)) := ((W.mulVecLin).toContinuousLinearMap).contDiff
lemma cont_d {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (W : Matrix β α ℝ) {x : E→ Tabletop α} (h : ContDiffAt ℝ ω x 0) : ContDiffAt ℝ ω (fun z=> quill W (x z)) 0 := (quill_smooth W).contDiffAt.comp _ h
omit [Fintype β] in
lemma ink_quill (u : Tabletop ι→Tabletop α) (hs : ContDiffAt ℝ ω u 0) (i : β) : ink (fun x=> quill W (u x) i) = quill W (fun j:α=> ink (fun x=>u x j)) i := by
  unfold quill; rw [show (fun x=>∑ j:α,W i j • u x j)=∑ j:α,W i j • (fun x=>u x j) by ext; simp,ink_sum]; swap; · exact fun j _=> (contDiffAt_pi.mp hs j).const_smul (W i j)
  exact sum_congr rfl fun j _=> ink_scale (contDiffAt_pi.mp hs j) _
omit [Fintype β] in
lemma flash_quill (u : Tabletop ι→Tabletop α) (hs : ContDiffAt ℝ ω u 0) (hu : u 0=0) (i : β) : flash (fun x=> quill W (u x) i)=quill W (exposure u) i := by
  have he j : X * exposure u j = ink (fun x=>u x j) := flash_origin (f:=fun x=>u x j) (hu ▸ rfl)
  apply X_mul_cancel; rw [flash_origin (f:=fun x=>quill W (u x) i) (by rw [hu, quill_zero]; rfl), ink_quill u hs]; unfold quill; simp_rw [mul_sum, mul_smul_comm, he]

-- real itinerary through seat; equality of algebraic `submit` on a composed channel
variable {u v : Tabletop α→Tabletop β} {U : Tabletop κ→Tabletop α} {V : Tabletop α→Tabletop ι}
omit [Fintype ι] in
lemma exposure_quill (W : Matrix ι β ℝ) (hu : ContDiffAt ℝ ω u 0) (hx : u 0=0) : exposure ((quill W (A:=ℝ)) ∘ u)=quill W (exposure u) := by ext1 i; exact flash_quill u hu hx i
omit [Fintype ι] in
lemma exposure_quill_apply (W : Matrix ι β ℝ) : exposure (quill W (A:=ℝ))=quill W named := by simpa [exposure_id] using exposure_quill W (u:=id) contDiffAt_id (id_eq 0)
lemma exposure_plus (hu : ContDiffAt ℝ ω u 0) (hv : ContDiffAt ℝ ω v 0) (h : u 0=0) (hh : v 0=0) : exposure (u+v)= exposure u+exposure v := by
  ext1 i; exact flash_expands (contDiffAt_pi.mp hu i) (contDiffAt_pi.mp hv i) (congr_fun h i) (congr_fun hh i)
lemma expose_assoc (hv : ContDiffAt ℝ ω v 0) (hx : v 0=0) (hu : ContDiffAt ℝ ω U 0) (hh : U 0=0) :
    exposure (v ∘ U)= (fun i=> submit (exposure U) (exposure v i)) := by
  ext1 i; let k:=fun x=> v x i
  have ht : (fun x:Tabletop κ=> (v ∘ U) x i)= k ∘ U:= rfl
  change flash (k∘ U)= submit (exposure U) (flash k)
  exact flash_comp (f:=k) (contDiffAt_pi.mp hv i) (congr_fun hx i) hu hh
lemma exposure_encode (hu : ContDiffAt ℝ ω U 0) (hv : ContDiffAt ℝ ω v 0) (hU : U 0=0) (hx : v 0=0) (p : Tape β) :
    submit (exposure U) (submit (exposure v) p) = submit (exposure (v ∘ U)) p := by rw [submits,expose_assoc hv hx hu hU]
omit [Fintype β] [Fintype ι] in
lemma expose_assemble : exposure (fun z : Tabletop α=> Sum.elim (u z) (V z))=Sum.elim (exposure u) (exposure V) := funext fun i=> by cases i <;> rfl
lemma assemble_jet (hu : ContDiffAt ℝ ω u 0) (hv : ContDiffAt ℝ ω V 0) : ContDiffAt ℝ ω (fun z=> Sum.elim (u z) (V z)) 0 := (assemble β ι).contDiff.contDiffAt.comp _ (hu.prodMk hv)
omit [Fintype β] in
lemma expose_match (he : u=ᶠ[𝓝 0] v) : exposure u=exposure v := funext fun j=> flash_of (he.mono fun _ h=> congr_fun h j)
omit [Fintype α] [Fintype β] [Fintype ι] in
lemma assemble_zero (hu : u 0=0) (hv : V 0=0) : Sum.elim (u 0) (V 0)=0 := by rw [hu,hv]; ext1 i; cases i <;> rfl
-- arbitrary dressing old dimension to new along pull π
variable (θ : Tabletop (Chamber α ι)→Tabletop α)
def ride (z : Tabletop (Chamber α ι)) := Sum.elim (θ z) (lower α ι z)
lemma ride_zero (hθ : θ 0=0) : ride θ 0=0 := assemble_zero hθ (map_zero (lower α ι))
lemma ride_jet (hθ : ContDiffAt ℝ ω θ 0) : ContDiffAt ℝ ω (ride θ) 0 := assemble_jet hθ (lower α ι).contDiff.contDiffAt
lemma ride_pull (f : StageD α ι) : submit (exposure (ride θ)) f=switch (exposure θ) f := by unfold ride; rw [expose_assemble (V:=lower _ _),lower_code]; rfl
@[simp] lemma lower_ride (z : Tabletop (Chamber α ι)) : lower α ι (ride θ z)=lower α ι z := rfl
@[simp] lemma upper_ride (z : Tabletop (Chamber α ι)) : upper α ι (ride θ z)= θ z:= rfl
end YM.WilsonBulk.Sheet
