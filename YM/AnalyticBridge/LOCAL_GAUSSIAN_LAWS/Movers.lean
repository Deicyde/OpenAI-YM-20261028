import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.CutGerm
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Removable


/-!
# On any remote patch: price true affine move against its flat *cut*
release with same F. Space of all enrolable Active colors. Include price
of sums over possible support using growth *only of one fixed integer ball*
at torus sizes. No number of walks hidden--it's in the path's weight.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Remote
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure  Pressure.Stores Gaussian Tree Wisps Bid
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f} {x : ℝ}

section Probe
variable (A : Stores S) (F : Forest S.ratio)
def rod (j : Rows.In x A F (G:=G)) := fresh x (shots S x) A F (axisPrice j)
lemma readRod (j : Rows.In x A F (G:=G)) : rod A F j=Pi.single j.1.val.val (EuclideanSpace.basisFun G.ColorIndex ℝ j.2) := by
  funext i; rw [Pi.single_apply]; split
  next h => rw [h,rod,Gap.freshly_read,on_axis,Pi.single_eq_same]
  next h =>
    unfold rod fresh; split
    · rename_i hi; split; rename_i hx
      · have h0 : (⟨⟨i,hi⟩,hx⟩:Active A x F) ≠ j.1 := fun he => h (congr_arg (fun a : Active A x F => a.val.val) he)
        rw [on_axis,Pi.single_eq_of_ne h0]
      · rfl
    · rfl
lemma rod_norm (j : Rows.In x A F (G:=G)) : ‖rod A F j‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr fun k => ?_
  rw [readRod,Pi.single_apply]; split <;> simp
lemma invoiced (j : Rows.In x A F (G:=G)) {o : Site c} {D : ℕ} (h : separation o (front A F j)≤D) : invoice S (rod A F j) o D := by
  intro e he
  rw [readRod,Pi.single_apply,if_neg]; rintro rfl'; rw [rfl'] at he; exact he h

lemma move_read (T : Tube G S) (V : Config G c) (k : S.Choices) (hp : S.patch.Branches S.kernel G) (i : Receipt G S) (j : In x A F (G:=G)) :
    move T x V k (shots S x) A F i j=tape.symm (slip • bump T x V k (rod A F j)) i := by
  unfold move; rw [Matrix.of_apply,selected_all T x V k A F _ hp]; rfl

lemma move_empty (T : Tube G S) (V : Config G c) (k : S.Choices) (hp : S.patch.Branches S.kernel G) (i : Receipt G S) (j : In x A F (G:=G))
    (he : span S.patch x<separation (front A F j) (down S i)) :
    move T x V k (shots S x) A F i j=0 := by
  rw [move_read A F T V k hp]
  change (slip • bump T x V k _ i.1) i.2=0
  rw [bump_dep T x V k i.1.1 i.1.2 (rod A F j) 0 hp (by
    intro e hx; rw [readRod,Pi.single_apply,if_neg]; rfl
    intro hz; rw [hz] at hx; have hv := (contains ..).mp hx
    rw [separation_comm] at he; exact (not_le_of_gt he) hv),show bump T x V k 0 i.1=(0:G.Color) from (by
      obtain ⟨⟨s,a|b⟩,i⟩:=i; simp [bump,faceKick,barrel]; simp [bump,noiseKick]),smul_zero]
  rfl

def official (j : Rows.In x A F (G:=G)) : Rows.In x (bareStores S) F (G:=G) :=
  Assembly.opened G S x _ F (Assembly.bare_is_Clear S x F) (j.1.val,j.2)

lemma corresponding (T : Tube G S) (V : Config G c) (k : S.Choices) (hp : S.patch.Branches S.kernel G) :
    move T x V k (shots S x) A F = (move T x V k (shots S x) (bareStores S) F).submatrix id (official A F) := by
  ext i j; rw [move_read ..,Matrix.submatrix_apply,move_read (S:=S) (x:=x) ..,readRod A,readRod]
  rfl
  exact hp
  exact hp
lemma corresponding_gram (T : Tube G S) (V : Config G c) (k : S.Choices) (hp : S.patch.Branches S.kernel G) :
    Rows.gram T x V k (shots S x) A F = (Rows.gram T x V k (shots S x) (bareStores S) F).submatrix (official A F) (official A F) := by unfold Rows.gram; rw [corresponding A F T V k hp]; rfl
end Probe

def pieces (P : Patch) (G : Gauge) := (Fintype.card Signed:ℝ)*((Fintype.card (Site P.L)*Fintype.card PlaqAxes*2+Fintype.card Axis:ℝ)*Fintype.card G.ColorIndex)
lemma pieces_nonneg (P : Patch) (G : Gauge) : 0≤pieces P G := by unfold pieces; positivity

lemma sum_down (G : Gauge) (S : StepData c f) (v : Site c→ℝ) :
    ∑ i : Receipt G S, v (down S i) = pieces S.patch G * ∑ i, v i := by
  unfold pieces
  have hh {s : Signed} : v ∘ (s.act : Site c → Site c) = v ∘ StepData.sendSites s 0 := by funext i; simp [StepData.sendSites]; rfl
  have hv (s : Signed) : ∑ i,v (s.act i) = ∑ i,v i := by
    rw [show (fun i => v (s.act i)) = v ∘ (s.act:Site c→Site c) from rfl,hh]; exact Equiv.sum_comp _ _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type,Fintype.sum_sum_type,sum_add_distrib,Wisps.down,roots,Sum.elim_inl,Sum.elim_inr, Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hz (s : Signed) : ∑ i,v (s.act (S.ratio.parent i))=(Fintype.card (Site S.patch.L):ℝ)*∑ i,v i := (Work.F01.sum_parent S.ratio (fun i => v ((s:Signed).act i))).trans (by rw [hv]; rfl)
  simp_rw [← Finset.mul_sum,hz,hv]; simp; ring

lemma down_count (G : Gauge) (S : StepData c f) (d : ℕ) (o : Site c) :
    ∑ i : Receipt G S, (if separation o (down S i) ≤ d then (1:ℝ) else 0) ≤ pieces S.patch G * LocalJet.grain d := by
  rw [sum_down G S (fun i => if separation o i ≤ d then 1 else 0)]
  exact mul_le_mul_of_nonneg_left (by simp_rw [separation_comm o]; exact LocalJet.spends _ _) (pieces_nonneg ..)

def wiggle (x A t : ℝ) := A*(1+(till x:ℕ))*t
def matter (G : Gauge) (P : Patch) (x A t : ℝ) :=
  (pieces P G*LocalJet.grain (span P x)) * ((A+wiggle x A t)*(wiggle x A t)+(wiggle x A t)*A)
lemma wiggle_nonneg (x : ℝ) {A t : ℝ} (hA : 0≤A) (ht : 0≤t) : 0≤wiggle x A t := by unfold wiggle; positivity
lemma matter_nonneg (G : Gauge) (P : Patch) (x : ℝ) {A t : ℝ} (hA : 0≤A) (ht : 0≤t) : 0≤matter G P x A t := by
  have hx := pieces_nonneg P G; have ht := wiggle_nonneg x hA ht
  unfold matter LocalJet.grain; positivity
lemma stamps (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (C : ℝ) (hp : P.Branches K G) (hC : 0≤C) :
    ∃ A δ : ℝ, 0≤A ∧ 0<δ ∧ ∀ t : ℝ, 0≤t → t ≤ δ → ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ (T : Tube G S) (Λ σ : ℝ), T.high=p → T.up.Bounds p σ C Λ → ∀ (x : ℝ) (o : Site c) (D : ℕ) (V : Config G c),
    paid S (replica S.ratio V) o D t → ∀ (k:S.Choices) (X : Stores S) (F : Forest S.ratio) (i : Receipt G S) (j : In x X F (G:=G)),
    separation o (Wisps.down S i)+span P x ≤ D → separation o (front X F j) ≤ D →
    |Rows.move T x V k (shots S x) X F i j - Rows.move T x (1:Config G c) k (shots S x) X F i j| ≤ wiggle x A t ∧
      |Rows.move T x (1:Config G c) k (shots S x) X F i j| ≤ A := by
  obtain ⟨A,δ,hA,hδ,H⟩ := pulse_bill G P K p C hp hC
  refine ⟨slip*A,δ,mul_nonneg slip_pos.le hA,hδ,?_⟩
  intro t ht he c f S hP hK T Λ σ hT hv x o D V H1 k X F i j h1 h2
  let z:=rod X F j
  obtain ⟨hh,hs⟩ := H t ht he S hP hK T Λ σ hT hv x o D V H1 _ (rod_norm ..) (invoiced X F _ h2) k i.1 h1
  have hp : S.patch.Branches S.kernel G := by rw [hP,hK]; exact hp
  rw [move_read ..,move_read ..]
  let a:=(slip • bump T x V k z i.1); let b:=slip • bump T x (1:Config G c) k z i.1
  change |a i.2-b i.2|≤_ ∧ |b i.2|≤_
  have hw (v : G.Color) : |v i.2| ≤ ‖v‖ := by rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ v i.2]; simpa using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i.2) v
  refine ⟨(hw (a-b)).trans ?_,(hw b).trans ?_⟩
  · unfold a b; rw [← smul_sub,norm_smul,Real.norm_of_nonneg slip_pos.le]; exact (mul_le_mul_of_nonneg_left hh slip_pos.le).trans_eq (by unfold wiggle; ring)
  unfold b; rw [norm_smul,Real.norm_of_nonneg slip_pos.le]; exact (mul_le_mul_of_nonneg_left hs slip_pos.le)
  all_goals exact hp

theorem local_gram (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (C : ℝ) (hp : P.Branches K G) (hC : 0≤C) :
    ∃ A δ : ℝ, 0≤A ∧ 0<δ ∧ ∀ t : ℝ, 0≤t → t ≤ δ → ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ (T : Tube G S) (Λ σ : ℝ), T.high=p → T.up.Bounds p σ C Λ → ∀ (x : ℝ) (o : Site c) (D : ℕ) (V : Config G c),
    paid S (replica S.ratio V) o D t → ∀ (k:S.Choices) (X : Stores S) (F : Forest S.ratio) (j z : In x X F (G:=G)),
    separation o (front X F j)+span P x+span P x ≤ D → separation o (front X F z) ≤ D →
    let reAddr := official X F
    |Rows.gram T x V k (shots S x) X F j z - Rows.gram T x (1:Config G c) k (shots S x) (bareStores S) F (reAddr j) (reAddr z)| ≤ matter G P x A t := by
  obtain ⟨A,δ,hA,hδ,H⟩ := stamps G P K p C hp hC
  refine ⟨A,δ,hA,hδ,?_⟩
  intro t ht he c f S hP hK T Λ σ hT hv x o D V H1 k X F i j h1 h2 E
  let a:= move T x V k (shots S x) X F; let b:=move T x (1:Config G c) k (shots S x) X F
  let w:=wiggle x A t; have hw : 0≤w := wiggle_nonneg x hA ht
  let v:=front X F i
  change |(a.transpose*a) _ _-(Rows.gram T x 1 k (shots S x) (bareStores S) F).submatrix E E i j|≤_
  have hh : S.patch.Branches S.kernel G := by rw [hP,hK]; exact hp
  rw [show (Rows.gram T x 1 k (shots S x) (bareStores S) F).submatrix E E=b.transpose*b from (corresponding_gram X F T 1 k hh).symm,mul_apply,mul_apply,← sum_sub_distrib]
  let B (z : Receipt G S) := if separation v (Wisps.down S z)≤span P x then (1:ℝ) else 0
  refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun i => B i * ((A+w)*w+w*A)) (fun z _ => ?_)).trans ?_)
  · unfold B; split
    next hs =>
      have hl : separation o (Wisps.down S z)+span P x ≤ D := by have hx := separation_triangle o v (Wisps.down S z); unfold v at hx hs; omega
      obtain ⟨hi,hI⟩ := H t ht he S hP hK T Λ σ hT hv x o D V H1 k X F z i hl (by omega)
      obtain ⟨hj,hJ⟩ := H t ht he S hP hK T Λ σ hT hv x o D V H1 k X F z j hl h2
      have ha : |a z i|≤A+w := calc
        _ = |a z i-b z i+b z i| := by rw [sub_add_cancel]
        _ ≤ _ := (abs_add_le ..).trans ((add_le_add hi hI).trans_eq (add_comm ..))
      change |a z i*a z j - b z i*b z j| ≤ _
      rw [one_mul,show a z i*a z j - b z i*b z j=a z i*(a z j-b z j)+(a z i-b z i)*b z j by ring]
      apply (abs_add_le ..).trans; rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul ha hj (abs_nonneg _) (by positivity)) (mul_le_mul hi hJ (abs_nonneg _) hw)
    next hs =>
      have hx : span S.patch x < separation v (Wisps.down S z) := hP.symm ▸ (lt_of_not_ge hs)
      change |a z i*a z j-b z i*b z j|≤_; unfold a b; rw [move_empty X F T V k hh z i hx,move_empty X F T (1:Config G c) k hh z i hx]; simp
  rw [← sum_mul]; unfold matter B
  rw [← hP] -- converts price and test
  exact mul_le_mul_of_nonneg_right (down_count G S _ v) (by change 0≤(A+w)*w+w*A; positivity)
end YM.AnalyticBridge.LocalGaussianLaws.Remote
