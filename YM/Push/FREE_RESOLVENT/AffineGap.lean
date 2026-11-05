import YM.Push.FREE_RESOLVENT.Affine
import YM.Work.F08.Rows

/-!
# The free affine Precision's own gap

No-hole or arbitrary principal compression, data at flat. This time only the
canonical **direct** channel is needed for the positive lower constant (so
we may pay for it even after cutting path lengths BEFORE projecting to a
metric). No dependence on radius. Identify uncut matrix with the tree free
one when using Attach + path inputs at use cases. Don't assume every such
PathData is available.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {n c f : Side} {S : StepData c f}

lemma response_zero (s : Signed) (y : Vec G f 1) :
    response S s 0 *ᵥ y = flatten (dColor G f 1 (pulled (decode y) s)) := by
  have he := face_path S s 0 y
  funext ⟨x,i,j⟩
  obtain ⟨p,hp⟩ := plaqEquiv.surjective i
  rw [plaq_map] at hp; subst i
  have hh := hasDerivAt_pi.mp he (x,plaquette p,j)
  simp only [faces,rays,back_recover, represent_pulled, show plaqEquiv.symm (plaquette p)=p from plaqEquiv.symm_apply_apply _] at hh
  exact hh.unique ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) j).hasFDerivAt.comp_hasDerivAt _ (curvature_of_hasDerivAt (face_deriv (x,p) _)))

lemma duct_zero (hb : S.patch.Branches S.kernel G) (s : Signed) (k : S.Choices) (v : Vec G f 1) :
    duct S s k 0 *ᵥ v=flatten (pulled (bills S (decode v)) s) := by
  have hp (x : Body 1 c) := (duct_path hb s k).self_of_nhds x v
  suffices H : decode (duct S s k 0 *ᵥ v)=pulled (bills S (decode v)) s by rw [← H]; rfl
  funext x; rcases x with ⟨x,i⟩
  obtain ⟨j,hj⟩ := axisEquiv.surjective i; rw [coord_map] at hj; subst i
  apply G.colorMat_injective
  apply HasDerivAt.unique (hp (x,coord j))
  have he : S.prediction (1 : Config G f) k=1 := funext fun i => Push.settled S hb i k
  let X := posDir j; let Y := X.rotate s; let y := affine s 0 x
  let w := Y.used y
  have H : HasDerivAt (fun a : ℝ => G.mat (S.prediction (represent (a • decode v)) k w))
      (G.colorMat (bills S (decode v) (w.1, coord w.2))) 0 := Push.prices S hb w k _
  simp only [which,castNoise,back_flat, show axisEquiv.symm (coord j)=j from axisEquiv.symm_apply_apply _,he, Lattice.pull,
      Step.read, Pi.one_apply, inv_one,ite_self,mul_one,back_recover]
  let c := bills S (decode v)
  have hv : pulled c s (x,coord j) = if Y.neg then -c (w.1,coord w.2) else c (w.1,coord w.2) := by
    unfold pulled
    rw [show axisEquiv.symm (coord j)=j from axisEquiv.symm_apply_apply _]
  change HasDerivAt (fun a : ℝ => G.mat (if Y.neg then _ else _)) (G.colorMat (pulled c s (x,coord j))) _
  rw [hv]; split <;> rename_i hg
  · simp only [map_neg]; rw [← G.colorMat_skew]; exact H.star
  simpa only [hg, Bool.false_eq_true, ↓reduceIte] using! H

lemma pulled_inner (s : Signed) (u v : Dir G c) :
    dotProduct (flatten (pulled u s)) (flatten (pulled v s))=dotProduct (flatten u) (flatten v) := by
  rw [flat_dot,flat_dot]
  let E := Equiv.prodCongr (Equiv.refl (Site c)) axisEquiv
  rw [← E.sum_comp fun i => inner ℝ (pulled u s i) (pulled v s i), ← E.sum_comp fun i => inner ℝ (u i) (v i),
    ← Equiv.sum_comp (StepData.sendBonds (c:=c) s 0) (fun i => inner ℝ (u (E i)) (v (E i)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  change inner ℝ (pulled u s (i.1,coord i.2)) (pulled v s (i.1,coord i.2)) = inner ℝ (u (E (sendEdge s 0 i))) (v (E (sendEdge s 0 i)))
  unfold pulled; rw [show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply _]; dsimp only; split
  · rw [inner_neg_neg]; rfl
  rfl

lemma pull_id (a : Dir G n) : pulled a 1=a := by
  funext i; rcases i with ⟨x,i⟩; obtain ⟨j,hj⟩ := axisEquiv.surjective i; rw [coord_map] at hj; subst i
  unfold pulled; rw [show axisEquiv.symm (coord j)=j from axisEquiv.symm_apply_apply _]; dsimp only; rw [Step.rotate_one]; simp [posDir,Step.used,affine]

lemma channel_qf (S : StepData c f) (s : Signed) (k : S.Choices) (p : Clip) (W : PathData G) (r : Admit)
    (B : Vec G c 1) (x y : Vec G f 1) :
    let R := response S s B; let D := tracks S s W r B*R; let Q := duct S s k B
    dotProduct x (channel S s k p W r B *ᵥ y)=p.direct*dotProduct (R *ᵥ x) (R *ᵥ y)+dotProduct (D *ᵥ x) (D *ᵥ y)+
      S.kernel.penalty*dotProduct (Q *ᵥ x) (Q *ᵥ y) := by
  intro R D Q
  have h {ι : Type} [Fintype ι] (R : Matrix ι (raw G f) ℝ) : dotProduct x (squareQ R *ᵥ y)=dotProduct (R *ᵥ x) (R *ᵥ y) := by
    rw [squareQ, ← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]
  simp only [channel, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,dotProduct_smul, h]
  rfl

lemma channels (S : StepData c f) (k : S.Choices) (p : Clip) (W : PathData G) (r : Admit)
    (B : Vec G c 1) (x y : Vec G f 1) :
    dotProduct x (block S k p W r B *ᵥ y)=(Fintype.card Signed:ℝ)⁻¹ *
      ∑ s, dotProduct x (channel S s k p W r B *ᵥ y) := by
  rw [block,Matrix.smul_mulVec,Matrix.sum_mulVec,dotProduct_smul, dotProduct_sum]; rfl

def headGap (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) :=
  (Fintype.card Signed:ℝ)⁻¹ * treeFare G P K p.direct
lemma headGap_pos (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) : 0 < headGap G P K p := by
  have hi : 0 < (Fintype.card Signed:ℝ) := by exact_mod_cast Fintype.card_pos
  exact mul_pos (inv_pos.mpr hi) (treeFare_pos _ _ _ p.quadratic_pos)
lemma directGap (S : StepData c f) (T : Forest S.ratio) (k : S.Choices) (p : Clip) (W : PathData G) (r : Admit)
    (hp : Larger (G:=G) S) : Gap (primary S T k p W r 0) (headGap G S.patch S.kernel p) := by
  let H := Work.F08.scaleRows p.direct (Work.F08.unitRow (TypeFace 2))
  have he : H.acts f=p.direct • 1 := by unfold H; rw [Work.F08.acts_scale, Work.F08.acts_unit]
  have hv := tree_gap S T H hp p.quadratic_pos (show Gap (H.acts f) p.direct from ⟨fun w => by
    rw [he, Matrix.smul_mulVec,Matrix.one_mulVec, dotProduct_smul]; exact le_rfl⟩)
  constructor; intro v
  let x := insertion (plant T)*ᵥ v
  let y := decode x
  have hV := hv.lower v
  rw [primary, ← insertion.dot_compress, channels, headGap,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_trans _ (Finset.single_le_sum (a:=(1:Signed)) (s:=Finset.univ) (fun i _ => ?_) (Finset.mem_univ _))
  · apply hV.trans
    rw [treeMatrix,← insertion.dot_compress,channel_qf]
    simp only [← Matrix.mulVec_mulVec, response_zero,duct_zero hp.1, pull_id]
    let R := tracks S 1 W r 0
    let c := flatten (dColor G f 1 y)
    change dotProduct (flatten y) (fullMatrix G S H *ᵥ flatten y) ≤ p.direct*dotProduct c c+dotProduct (R *ᵥ c) (R *ᵥ c)+_
    rw [fiscal_eq, ← flat_dot]
    apply add_le_add
    · apply le_trans _ (le_add_of_nonneg_right (normSum_nn _))
      unfold curlCharge; rw [component_dot, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => le_of_eq ?_
      rw [Precision.K, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec, he, Matrix.smul_mulVec,Matrix.one_mulVec,smul_dotProduct]; rfl
    exact le_rfl
  rw [channel_qf]
  exact add_nonneg (add_nonneg (mul_nonneg p.quadratic_pos.le (normSum_nn _)) (normSum_nn _))
    (mul_nonneg S.kernel.penalty_pos.le (normSum_nn _))


-- Exact flat glue lemma. Only for paths when *attached*. Roots symmetry inputs
-- from Rack producers will still have to be earned before using it there. We
-- don't consume diagonal/Bed.inverse or any T trackers in this identification.
section identify
variable {W : PathData G} {p : Clip} {B : Bed} {σ C Λ : ℝ}

lemma identity_track (S : StepData c f) (s : Signed)
    (h : W.Bounds p σ C Λ) (ht : Attached B W) :
    tracks S s W (fun _ => true) 0=tensor G (B.roots.acts f) := by
  ext ⟨x,b,i⟩ ⟨y,a,j⟩
  obtain ⟨q,hq⟩ := plaqEquiv.surjective b
  obtain ⟨z,hz⟩ := plaqEquiv.surjective a
  rw [plaq_map] at hq hz; subst b; subst a
  have hv : shone S s (0 : Vec G c 1) = 1 := by rw [shone, back_flat]; ext; simp [Lattice.pull,Step.read]
  rw [tensor,Matrix.of_apply, tracks,Matrix.of_apply]
  have hh : plaqEquiv.symm (plaquette q)=q := plaqEquiv.symm_apply_apply _
  have hw (P : RG.Slot) : travel (shone S s (0:Vec G c 1)) x P.walk=1 := by
    rw [hv, ← Precision.link_one]; exact Push.stroll_zero ..
  let F (k : ℕ) := W.row q k
  have hT (k : ℕ) : edgework S s W (fun x => true) (x,plaquette q,i) (y,plaquette z,j) k 0 =
      if i=j then if slotFace (F k).2 x=(y,z) then (F k).1 else 0 else 0 := by
    unfold edgework; rw [hh]; simp only [if_true,element]
    -- collapse basis
    simp only [Prod.mk.injEq, plaq_iff, slotFace]
    rw [hw, Gauge.adjoint_one]
    by_cases h : i=j
    · subst j; simp [F,eq_comm]
    simp [h]
  simp_rw [hT]
  split
  · exact (layout_physical B h ht (x,q) (y,z)).tsum_eq
  rw [tsum_zero]

lemma identifies (S : StepData c f) (T : Forest S.ratio) (k : S.Choices)
    (ha : S.patch.Branches S.kernel G) (h : W.Bounds p σ C Λ) (ht : Attached B W)
    (hr : (B.full p f).transpose * B.full p f=B.metric.acts f) (hs : Bid.Sworn B f G) :
    primary S T k p W (fun _ => true) 0 = treeMatrix G S T B.metric := by
  have he : B.metric.acts f = p.direct • 1 + (B.roots.acts f).transpose * B.roots.acts f := by
    rw [← hr]
    -- stack by sums: prove dot j
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type,
        Matrix.transpose_apply,Bed.full,Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib]; congr 1
    have hu : Real.sqrt p.direct * Real.sqrt p.direct = p.direct := by rw [← sq, Real.sq_sqrt p.quadratic_pos.le]
    let I : Matrix (Body 2 f) (Body 2 f) ℝ := 1
    calc
      _ = p.direct * ∑ l : Body 2 f, I l i * I l j := by
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x _; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_
        change Real.sqrt p.direct * I _ i * (Real.sqrt p.direct * I _ j) = _
        change Real.sqrt p.direct * I _ i * (Real.sqrt p.direct * I _ j) = p.direct * _
        linear_combination (I (x,l) i*I (x,l) j)*hu
      _ = _ := by
        change p.direct*(I.transpose*I) i j = _; simp [I]
  suffices heq : block S k p W (fun _ => true) 0=fullMatrix G S B.metric by rw [primary,treeMatrix,heq]
  have hu (x y : Vec G f 1) : dotProduct x (block S k p W (fun _ => true) 0 *ᵥ y) =
      dotProduct x (fullMatrix G S B.metric *ᵥ y) := by
    rw [channels]
    let u := decode x; let v := decode y
    have H (s : Signed) : dotProduct x (channel S s k p W (fun _ => true) 0 *ᵥ y)=
        dotProduct (flatten u) (fullMatrix G S B.metric *ᵥ flatten v) := by
      rw [channel_qf,fiscal_eq]
      simp_rw [← Matrix.mulVec_mulVec, identity_track S s h ht, response_zero, duct_zero ha s, pulled_inner, ← flat_dot]
      congr 1
      · let g := pulled u s; let h := pulled v s
        let U := flatten (dColor G f 1 g)
        let V := flatten (dColor G f 1 h)
        let R := B.roots.acts f
        have hn (i : G.ColorIndex) : component U i=d 1 f *ᵥ parts G 1 g i := rfl
        have hm (i : G.ColorIndex) : component V i=d 1 f *ᵥ parts G 1 h i := rfl
        change p.direct*dotProduct U V + dotProduct (tensor G R *ᵥ U) (tensor G R *ᵥ V)=gaugeFiscal B u v
        rw [← hs s u v]; change _ = gaugeFiscal B g h; rw [component_dot, component_dot,Finset.mul_sum,← Finset.sum_add_distrib]
        unfold gaugeFiscal; refine Finset.sum_congr rfl fun i _ => ?_
        simp only [component_mul, Precision.K,← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_transpose, ← hn, ← hm,he]
        rw [Matrix.vecMul_add, add_dotProduct, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, Matrix.vecMul_smul, Matrix.vecMul_one, smul_dotProduct]; rfl
    change _ = dotProduct (flatten u) (fullMatrix G S B.metric *ᵥ flatten v)
    simp only [H,Finset.sum_const, Finset.card_univ,nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_pos.ne'),one_mul]
  ext i j; simpa using hu (Pi.single i 1) (Pi.single j 1)
end identify
end YM.FreeResolvent.Affine
