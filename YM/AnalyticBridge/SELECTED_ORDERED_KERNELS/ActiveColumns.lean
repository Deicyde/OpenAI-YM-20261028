import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.TrueNoise
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.TrueTransport
import YM.Push.FREE_RESOLVENT.Columns
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Remainder

/-!
# Read the true selected `Rows.move` from the `market` chart's component matrices

Identity uses real `carry`/predictGroup orientation, color tangent extraction
AFTER facing the entire group path. A missing Q term on an active column
means `skip_bump`, identically zero. No inference about regularity on the
complement. Matrix read of barrel adapted from Columns (`element` sum of
TRUE path evaluations on physical copy).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Selected
open Lattice Wilson RG Precision Exterior Tree Function Filter Topology Bloch Next.SectorChange Next.Fluctuations
  Rows YM.Pressure YM.Pressure.Stores FreeResolvent Affine TestD Push.Uniform Matrix
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
  {x : ℝ} {A : Stores S} {T U : Forest S.ratio} {k : S.Choices} {V : Config G c}
  {W : PathData G} {s : Signed} {B : Vec G c 1}

def attach (A : Stores S) (T : Forest S.ratio) (i : In (G:=G) x A T) : raw G f := hue i.1.val.val i.2
lemma attach_inj (G : Gauge) (A : Stores S) (T : Forest S.ratio) : Injective (attach (G:=G) (x:=x) A T) := by
  intro i j h
  apply Prod.ext
  · exact Subtype.ext (Subtype.ext ((edge_hue ..).symm.trans ((congr_arg edge h).trans (edge_hue ..))))
  exact congr_arg (fun e : raw G f => e.2.2) h

lemma fresh_unit (i : In (G:=G) x A T) : fresh x (shots S x) A T (axisPrice i) = unitDir (attach A T i) := by
  funext e
  rw [on_axis]
  by_cases he : e = i.1.val.val
  · subst e
    have he := unit_here (attach A T i)
    rw [show edge (attach A T i) = i.1.val.val from edge_hue ..] at he
    rw [he]
    simp only [fresh, dif_pos i.1.val.property, dif_pos i.1.property,Pi.single_eq_same,EuclideanSpace.basisFun_apply]; rfl
  have hh : e ≠ edge (attach A T i) := (edge_hue ..) ▸ he
  rw [unit_off _ _ hh]
  unfold fresh; split
  · split
    · rename_i h1 h2
      exact Pi.single_eq_of_ne (fun H : (⟨⟨e,h1⟩,h2⟩:Next.SectorChange.Active A x T)=i.1 => he (congr_arg (fun j : Next.SectorChange.Active A x T => j.val.val) H)) _
    rfl
  rfl

section vertical
variable {ι : Type*} [Fintype ι]
private lemma grad_eval {Z : pair G c f → ι → ℝ} (Q : Directions G f → G.Color) (place : G.ColorIndex → ι)
    (h : ∀ y j, Q (paint G f y) j = Z (B,y) (place j))
    (he : DifferentiableAt ℝ Z (B,0)) (i : raw G f) (j : G.ColorIndex) :
    fderiv ℝ Q 0 (unitDir i) j = matrix Z B (place j) i := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : G.ColorIndex => ℝ)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (φ:=fun _ => ℝ) (place j)))
  let M := (paint G f).symm.toContinuousLinearMap
  let H := fun z => Z (B,z)
  have hQ : Q = L ∘ H ∘ M := by
    funext a; ext j
    change Q a j = H (M a) _
    unfold H; rw [← h, show paint G f (M a)=a from ContinuousLinearEquiv.apply_symm_apply ..]
  have hh : DifferentiableAt ℝ H 0 := he.comp 0 ((differentiableAt_const _).prodMk differentiableAt_id)
  rw [hQ,(L.hasFDerivAt.comp _ ((map_zero M).symm ▸ hh.hasFDerivAt |>.comp 0 M.hasFDerivAt)).fderiv, matrix, LinearMap.toMatrix'_apply]
  change fderiv ℝ H 0 (M (unitDir i)) (place j) = _
  rw [show M (unitDir i)=Pi.single i 1 from ContinuousLinearEquiv.symm_apply_apply ..]; rfl
end vertical

def inFace (p : Cell f) (j : G.ColorIndex) : tile G f := (p.1,plaqEquiv p.2,j)

lemma face_grad (hp : DifferentiableAt ℝ (petals S V s) (B,0)) (p : Cell f) (i : raw G f) (j : G.ColorIndex) :
    plaquetteJet S (increment V (paint G c B)) s p (unitDir i) j = matrix (petals S V s) B (inFace p j) i := by
  apply grad_eval _ _ (fun y u => ?_) hp
  simp only [petals,NoHole.faceRow,inFace,Equiv.symm_apply_apply]; rfl

lemma noise_grad (H : Tube G S) (hp : DifferentiableAt ℝ (contacts x A T U k V s) (B,0)) (e : Bond c)
    (i : In (G:=G) x A T) (j : G.ColorIndex) (hS : S.patch.Branches S.kernel G) :
    noiseKick (increment V (paint G c B)) k (unitDir (attach A T i)) s e j = -Real.sqrt S.kernel.penalty * matrix (contacts x A T U k V s) B (hue e j) (attach A T i) := by
  by_cases h : shared x A T U s e
  · unfold noiseKick blockJet
    change -(Real.sqrt _ * ((fderiv ℝ _ _ _) : G.Color) j) = _
    rw [neg_mul]; congr 2
    apply grad_eval _ _ (fun y u => ?_) hp
    simp only [contacts,edge_hue,if_pos h]; rfl
  have hh := skip_bump H x (increment V (paint G c B)) k A T s (.inr e) (axisPrice i) hS (fun h' => h (Or.inl h'))
  rw [fresh_unit] at hh
  change noiseKick .. = (0:G.Color) at hh
  rw [hh]
  have he := grad_eval (0 : Directions G f → G.Color) (hue (G:=G) e) (Z:=contacts x A T U k V s)
    (fun y u => by simp only [contacts,edge_hue,if_neg h]; rfl) hp (attach A T i) j
  rw [← he]; simp

lemma reads_outline (V : Config G c) (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) {σ M : ℝ} (hs : 0 ≤ σ) (h : Sheet W σ M)
    (B : Vec G c 1) (C : fieldDir G f 2) (p : Face (Per f)) :
    HasSum (fun k : ℕ => let z := W.row p.2 k; if r z.2 then z.1 • (G.adjoint (travel (pull s 0 (landscape S V B)) p.1 z.2.walk)
      (C (wrap f z.2.offset+p.1,plaquette z.2.plaq))) else 0)
      (decode (over (NoHole.pathRows S s W r) V B *ᵥ flatten C) (p.1,plaquette p.2)) := by
  rcases p with ⟨x,p⟩
  let A (i) := W.row p i
  let F (i) := if r (A i).2 then (A i).1 • (G.adjoint (travel (pull s 0 (landscape S V B)) x (A i).2.walk)
    (C (wrap f (A i).2.offset+x,plaquette (A i).2.plaq))) else 0
  have ht : Summable fun i => |(A i).1| := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun i =>
    le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hs (show 0 ≤ ((A i).2.length:ℝ) by positivity)))) (h p).2.1
  have he k : ‖F k‖ ≤ |(A k).1| * ‖C‖ := by
    unfold F; split <;> rename_i H; swap; · rw [norm_zero]; positivity
    rw [norm_smul, Real.norm_eq_abs,G.norm_adjoint]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm C _) (abs_nonneg _)
  have hp := Summable.of_norm_bounded (ht.mul_right _) he
  change HasSum F _; rw [hp.hasSum_iff]
  symm; ext i
  let a : tile G f := (x,plaquette p,i)
  let L : G.Color →L[ℝ] ℝ := PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i
  have hh (j : tile G f) : Summable fun k => outline V S s W r a j k B := by
    refine Summable.of_norm_bounded ht fun k => ?_
    unfold outline
    dsimp only [a]; rw [show plaqEquiv.symm (plaquette p)=p from plaqEquiv.symm_apply_apply _]
    split
    · rw [norm_mul,Real.norm_eq_abs]; apply mul_le_of_le_one_right (abs_nonneg _)
      unfold element; split
      · have h : ‖(G.adjoint (travel (pull s 0 (landscape S V B)) x (A k).2.walk) (EuclideanSpace.basisFun G.ColorIndex ℝ j.2.2))‖=1 := by simp
        change |((G.adjoint _) _ : G.Color) _| ≤ _
        rw [← h]; simpa only [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one, one_mul] using
          abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i) (G.adjoint (travel (pull s 0 (landscape S V B)) x (A k).2.walk) (EuclideanSpace.basisFun G.ColorIndex ℝ j.2.2))
      simp
    rw [norm_zero]; exact abs_nonneg _
  change (∑ j, (∑' k, outline V S s W r a j k B)*flatten C j)=L (∑' b, F b)
  simp_rw [L.map_tsum hp, ← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun j _ => (hh j).mul_right (flatten C j))]; refine tsum_congr fun k => ?_
  let u := travel (pull s 0 (landscape S V B)) x (A k).2.walk
  unfold outline F
  dsimp only [a]
  rw [show plaqEquiv.symm (plaquette p)=p from plaqEquiv.symm_apply_apply _]
  by_cases h : r (A k).2=true
  · simp only [show r _=true from h,if_true,show W.row p k=A k from rfl]
    rw [map_smul,Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type,element, Prod.mk.injEq,ite_mul,mul_ite,mul_zero,smul_eq_mul,ite_and]
    -- move sums with conditions through sums
    rw [Finset.sum_eq_single (wrap _ (A k).2.offset+x)]
    · simp only [if_true, zero_mul]
      rw [Finset.sum_eq_single (plaquette (A k).2.plaq)]
      · simp_rw [if_true,mul_assoc,← Finset.mul_sum]
        let v := C (wrap f (A k).2.offset+x,plaquette (A k).2.plaq); congr 1; exact color_tile v u i
      · intro b _ hb; simp [hb]
      simp
    · intro y _ hy; simp [hy]
    simp
  · simp [A] at h; simp [A,h]

variable {σ M : ℝ} (hS : S.patch.Branches S.kernel G) (hp : DifferentiableAt ℝ (petals S V s) (B,0))
  (hn : DifferentiableAt ℝ (contacts x A T U k V s) (B,0))
  (hs : 0 ≤ σ) (hW : Sheet W σ M)
include hp hs hW
lemma reads_grad (R : ℕ) (p : Cell f) (i : raw G f) :
    let F := over (NoHole.pathRows S s W (shorter R)) V B
    let Q := matrix (petals S V s) B
    barrel W R (facade S s (increment V (paint G c B)) 0) (fun j => plaquetteJet S (increment V (paint G c B)) s j (unitDir i)) p = decode ((F*Q).col i) (p.1,plaqEquiv p.2) := by
  intro F Q
  unfold barrel; rw [fixed_facade,show (F*Q).col i=F *ᵥ (Q.col i) from ?_]
  · rw [← flat_decode (Q.col i)]
    erw [← (reads_outline V S s W (shorter R) hs hW B (decode (Q.col i)) p).tsum_eq]
    refine tsum_congr fun z => ?_
    simp only [shorter,decide_eq_true_eq]; split
    swap; · rfl
    let e := (W.row p.2 z).2
    rw [show plaquetteJet S (increment V (paint G c B)) s (Work.F03.slotFace e p.1) (unitDir i)=decode (Q.col i) _ from ?_]; rfl
    ext u; exact face_grad hp (Work.F03.slotFace e p.1) i u
  ext y; rfl

omit hW hs hp
variable (H : Tube G S) (j : In (G:=G) x A T) (u : G.ColorIndex)
include hS hn
lemma noise_column (b : Bond c) :
    Rows.move H x (increment V (paint G c B)) k (shots S x) A T ((s,.inr b),u) j =
      slip * (-Real.sqrt S.kernel.penalty * matrix (contacts x A T U k V s) B (hue b u) (attach A T j)) := by
  unfold Rows.move; rw [of_apply,tape_read,selected_all _ _ _ _ _ _ _ hS,fresh_unit,← noise_grad H hn b j u hS]; rfl

omit hn
include hp
lemma face_column (p : Cell f) :
    Rows.move H x (increment V (paint G c B)) k (shots S x) A T ((s,.inl (p,false)),u) j =
      slip * (Real.sqrt H.high.direct * matrix (petals S V s) B (inFace p u) (attach A T j)) := by
  unfold Rows.move; rw [of_apply,tape_read,selected_all _ _ _ _ _ _ _ hS,fresh_unit,← face_grad hp p]; rfl

include hs
lemma barrel_column (hW : Sheet H.up σ M) (p : Cell f) :
    Rows.move H x (increment V (paint G c B)) k (shots S x) A T ((s,.inl (p,true)),u) j =
      slip * ((over (NoHole.pathRows S s H.up (shorter (till x))) V B * matrix (petals S V s) B) (inFace p u) (attach A T j)) := by
  unfold Rows.move; rw [of_apply,tape_read,selected_all _ _ _ _ _ _ _ hS,fresh_unit]
  change slip * (barrel H.up (till x) (facade S s (increment V (paint G c B)) 0) (fun i => plaquetteJet S (increment V (paint G c B)) s i (unitDir (attach A T j))) p) u = _
  rw [reads_grad hp hs hW]; rfl
end YM.SelectedOrderedKernels.Selected
