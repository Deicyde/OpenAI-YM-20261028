import YM.RG08.Line.Fixer

/-!
# Use of the completed-matrix strip on harmonic mode tours
-/
noncomputable section
namespace YM.RG08.Line
open Stationary Function Set Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators Matrix
 open scoped Classical

set_option autoImplicit false
variable {G : Gauge} {P : Patch} {S K : KernelChoices} {L n m : Side}
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {σ C D : ℝ} {p : Momentum}

lemma spade_basic (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] : (Slab.basic α).spade (Slab.basic β)=Slab.basic _ := by
  unfold Slab.spade Slab.basic
  congr 1; funext p; exact spades_one

-- Convert from joint weighted counting to ordinary entry costs at *post*-L cost.
def bump (L : Side):= Real.exp (1*4) * (inch L)⁻¹
lemma bump_ge : 1 ≤ bump L := by
  have h₁ := inch_le L
  have h₂ := inch_pos L
  unfold bump; rw [← div_eq_mul_inv,le_div_iff₀ h₂,one_mul]
  exact h₁.trans (Real.one_le_exp (by norm_num))
lemma slab_basic (p : Momentum) (h : p ∈ strip 1) : serial (Slab.basic (ParcelG G L)) (slabW G L) p p 1 (bump L) := by
  have he := cruise (L:=L) (α:=Loc G 1) p h
  have hv := serial.free (X:=Slab.basic (Loc G 0)) (p:=p) |>.mono (bump_ge (L:=L))
  rw [slabW,← spade_basic, ← spades_one]; exact Slab.serial_spade he hv
lemma raw_matrix (h : p∈strip 1) {M : CompM (ParcelG G L) (ParcelG G L)} (he : serial (slabW G L) (slabW G L).dual p p M C) (i j) : ‖M i j‖ ≤ bump L * C * bump L := by
  let U := slabW G L; let V := Slab.basic (ParcelG G L)
  have hk : serial V U p p 1 (bump L) := slab_basic p h
  have hh : serial V U (-p) (-p) 1 (bump L) := slab_basic (-p) (negResident h)
  have ht : serial U.dual V p p 1 (bump L) := by simpa only [V,neg_neg,transpose_one,slide_basic] using hh.slide
  have hv := (hk.bond he).bond ht
  simp only [one_mul, mul_one] at hv
  unfold serial carryM at hv
  simp only [V,Slab.basic,inv_one,one_mul,mul_one] at hv
  exact (flux_tilt _ _ _).trans hv

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
lemma vane_tile {M: Momentum → CompM α β}(h:Poster σ M)(hs:0<σ)(i j): Vane (fun p=> M p i j) σ := by
  refine ⟨hs,fun p hp=> h.shape hp i j,fun p hp x=>?_⟩
  rw [← h.shifts (show rolls p (p+reciprocal x) from ⟨x,rfl⟩) hp]

lemma poster_inv {F : Momentum → CompM α α} (h : Poster σ F) (he : ∀ p∈strip σ, IsUnit (F p).det) : Poster σ fun p=> (F p)⁻¹ := ((Play.current (ι:=Unit) h).back he).tab

def beam (M : Momentum → CompM α β): Row α β := fun i j x=> (market (fun p=>M p i j) 0 x).re

def collect_price (σ C : ℝ) := C * (2*((1+σ/3)/(σ/3)))^4
lemma collect_price_nn (σ : ℝ) (h:0≤C) : 0 ≤ collect_price σ C := mul_nonneg h (by apply Even.pow_nonneg (by decide +kernel) _) -- decide Even?

 omit [DecidableEq β] [Fintype α] [Fintype β] [DecidableEq α] in
lemma beam_value {M : Momentum → CompM α β} (h : Poster σ M) (hs:0<σ) (he:∀ p∈strip σ,∀ i j, ‖M p i j‖≤C) :
    (beam M).strip (σ/3) (collect_price σ C) ∧
    ∀ p, star p=p → (beam M).read p = (1/2:ℂ) • (M p + (M (-p)).map star) := by
  have hv (i j):= vane_tile h hs i j
  have hX (i j) : Width (σ/3) (collect_price σ C) (market (fun p=> M p i j) 0):= by
    simpa only [collect_price, Axis, Fintype.card_fin] using (hv i j).issues (fun p hp=> he p hp i j) (σ/3) (σ/3) (by linarith) (by linarith) (by linarith)
  refine ⟨fun i j=> Work.F07.widthRealPart (hX i j),fun p hp=>?_⟩
  ext i j
  unfold beam
  rw [Row.read,Matrix.of_apply, Work.F07.readRealPart (hX i j) (by linarith) hp,
    (hv i j).paints (fun p hp=> he p hp i j) p (Work.F07.realStrip σ hs hp),
    (hv i j).paints (fun p hp=> he p hp i j) (-p) (Work.F07.realStrip σ hs (show star (-p)=-p by rw [star_neg,hp]))]
  simp; ring

def hessian (G : Gauge) {n m} (S : StepData n m) (t : S.Choices) (b : Bed) : CircM n (ParcelG G S.patch.L) (ParcelG G S.patch.L) := approached (repackM (clothe G S) (clothe G S)
    (frontR G S b + (postroom S t (inch S.patch.L))ᵀ * (postroom S t (inch S.patch.L))))

lemma hessian_pass {n m} (S : StepData n m) (t : S.Choices) (b : Bed) (h : S.patch.Branches S.kernel G) (hs:0 < σ) (ht:b.metric.strip (inch S.patch.L * σ) C) :
    Jaunt (hessian G S t b) (forceK G S.patch (fixSymbol G S.patch) S.kernel.penalty b) 0 := by
  let Y := unitSplit G S 0
  let V := clothe G S
  let W := postroom (G:=G) S t (inch S.patch.L)
  unfold hessian
  rw [show repackM V V (frontR G S b + Wᵀ*W)= repackM V V (frontR G S b)+ repackM V V (Wᵀ*W) from rfl,prom_addition,repack_multiply _ Y,repack_rotate, prom_mul]
  have he := unmasked S h t
  exact (gift_turn b hs ht).plus (he.takes.hoist he)

lemma image_back {x y : CompM α α} (h : yᵀ=xᴴ): y⁻¹ᵀ=x⁻¹ᴴ := by
  simp only [transpose_nonsing_inv, conjTranspose_nonsing_inv,h] -- name

 omit [DecidableEq α] [Fintype α] in
lemma jaunt_unique {A B : CircM m α β} {F : Momentum→CompM α β} (h : Jaunt A F 0) (hb : Jaunt B F 0) : A=B := by
  ext i j
  have he : A i = B i := by
    apply ray_book
    intro p b
    have hf := congr_fun ((h p _ (rolls.refl _) b).trans (hb p _ (rolls.refl _) b).symm) i
    exact (dotProduct_comm ..).trans (hf.trans (dotProduct_comm ..))
  exact congr_fun he j

 lemma jaunt_cash {A B : CircM m α α} {F : Momentum → CompM α α}(h:Jaunt A F 0)(ht:Jaunt B (fun p=> (F p)⁻¹) 0)(he:∀ p, star p = (p:Momentum) → IsUnit (F p).det) : A*B=1 := by
  -- explicit types, use compatible decEq instance for One
  have hg : Jaunt (A*B) (fun _=>1) 0:=by
    intro p r hr v
    have h1:= h.hoist ht p r hr v -- syntax
    refine Eq.trans h1 ?_
    dsimp only
    rw [Matrix.mul_nonsing_inv _ (he r (hr.metric (real_frequency p)))]
  exact jaunt_unique hg (Jaunt.noop (m:=m) (α:=α))

/-- From a Freezer strip to one real position-space inverse for all of this step's finite periods.
Norm costs only polynomial powers of L and the pre-block structural constants.
-/
theorem transcribe {b:Bed} (ht : P.Branches K G) (hP: Poster σ (forceK G P (fixSymbol G P) K.penalty b))
    (hG: Freezer (slabW G P.L).dual (slabW G P.L) (forceK G P (fixSymbol G P) K.penalty b) σ C)
    (hs:0<σ) (h:σ ≤ 1) (hk:b.metric.strip (inch P.L*σ) D) (_hC:0≤C) :
    let O:=forceK G P (fixSymbol G P) K.penalty b
    (beam fun p=> (O p)⁻¹).strip (σ/3) (collect_price σ (bump P.L*C*bump P.L)) ∧
    ∀ (n m: Side)(H:m.val=n.val*P.L.val)(t:(RG.StepData.mk P K H).Choices),
      hessian G (StepData.mk P K H) t b * approached ((beam fun p=> (O p)⁻¹).acts n)=1 := by
  intro O
  let a:= atSide P K
  have hZ i: Nonempty ((a.boot i).Choices):= inferInstance
  let t i:= Classical.choice (hZ i)
  have he1 : Poster σ O:=hP
  have he : Poster σ (fun p=> (O p)⁻¹):=poster_inv he1 hG.period
  obtain ⟨hV,hE⟩:=beam_value he hs (fun p hp i j=> raw_matrix (fun i=> (hp i).trans_le h) (hG.price p hp) i j)
  refine ⟨hV,fun n m H f=>?_⟩
  have hh i := hessian_pass (a.boot i) (t i) b ht hs hk
  have hy p (hp:star p = (p:Momentum)) : (O (-p))ᵀ=(O p)ᴴ := judge increasing (fun i=>hh i) he1 hs hp
  let Q : Row (ParcelG G P.L) (ParcelG G P.L) := beam fun p=> (O p)⁻¹
  have hx p (hp:star p = (p:Momentum)): Q.read p=(O p)⁻¹:= by
    ext i j; rw [show Q.read p= _ from hE p hp]
    have hI := congr_fun (congr_fun (image_back (hy p hp)) j) i
    change ((1/2:ℂ)*((O p)⁻¹ i j+star ((O (-p))⁻¹ i j)))=_
    change (O (-p))⁻¹ i j=star ((O p)⁻¹ i j) at hI; rw [hI,star_star]; ring
  have hF: Jaunt (approached (Q.acts n)) (fun p=> (O p)⁻¹) 0:=by
    intro p r hr v
    dsimp only
    rw [← hx r (hr.metric (real_frequency p))]
    exact Jaunt.row Q (Row.rights _ _ hV (by linarith)) p r hr _
  have hB : Jaunt (hessian G (StepData.mk P K H) f b) O 0 := hessian_pass (StepData.mk P K H) f b ht hs hk
  apply Eq.trans (jaunt_cash hB hF (fun r hr=> hG.period r (Work.F07.realStrip σ hs hr)))
  ext i j; simp [one_apply]
end YM.RG08.Line
