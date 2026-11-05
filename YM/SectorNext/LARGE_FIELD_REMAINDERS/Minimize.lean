import YM.SectorNext.LARGE_FIELD_REMAINDERS.Marginal
import YM.SectorNext.LARGE_FIELD_REMAINDERS.PairBound


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Buy single-center suppression on the actual cut remainder

No stationary/affine matrix used; buy centers common to the physical choices k for
one A at one V and one tree, at the intact-threshold prerequisites. Core need not
attain its minimum (flag discontinuities!). We don't ask these centers to be
compatible between different V's (nor that the minimization choice is measurable
in such an array); use on each density output separately. No assuming even positive
measure (or realizability) of each seeded sector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Center
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales Metric Oriented Presented Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}

private lemma complete {a : ℝ} (x y : G.Color) (h : ‖x‖ ≤ a) :
    ‖x-y‖^2/2 ≤ a^2/2 + (‖y‖^2/2-inner ℝ y x) := by
  rw [norm_sub_sq_real,real_inner_comm]
  nlinarith [norm_nonneg x]

lemma core_origin (T : Tube G S) (U : Config G f) (V Q : Config G c)
    (R : ℕ) (t s : ℝ) (i : Cell f) (j : Bond c) :
    ((toll U i ≤ t → PathData.kept T.high t i.1 U →
      ‖shiftedFine T R s V U i‖^2/2 ≤ T.workF R U V t s i) ∧
      ‖shiftedBond T R s V Q j‖^2/2 ≤ T.workI R Q V s j) := by
  constructor
  · intro h he
    let b := Real.sqrt T.high.direct
    have hb : 0≤b := Real.sqrt_nonneg _
    have h0 : ‖shoot T.high U i‖ ≤ b*toll U i := by
      rw [shoot,norm_smul,Real.norm_of_nonneg hb]; exact mul_le_mul_of_nonneg_left (G.curvature_norm _) hb
    have h1 := complete _ (T.Mv R s V (i,false)) h0
    have h2 := complete (shorten T.up R 1 U i) (T.Mv R s V (i,true)) le_rfl
    rw [workF,crown,trunk,if_pos he,PathData.clipped,if_pos (show G.chord _ ≤ t from h),Fintype.sum_bool]
    dsimp only [Xf,plotted]; simp only [Bool.false_eq_true,↓reduceIte]
    unfold shiftedFine
    rw [mul_pow,show b^2=T.high.direct from Real.sq_sqrt T.high.quadratic_pos.le] at h1
    unfold toll at h1
    nlinarith only [h1,h2, sq_nonneg ‖shorten T.up R 1 U i - T.Mv R s V (i,true)‖]
  · let b := Real.sqrt S.kernel.penalty
    have hb : 0≤b := Real.sqrt_nonneg _
    have h2 : ‖Z S Q V j‖≤b*wire Q V j := by unfold Z; rw [norm_smul,Real.norm_of_nonneg hb]; exact mul_le_mul_of_nonneg_left (G.curvature_norm _) hb
    have h1 := complete _ (T.Mw R s V j) h2
    rwa [mul_pow,show b^2=S.kernel.penalty from Real.sq_sqrt S.kernel.penalty_pos.le] at h1

lemma acts_origin (T : Tube G S) (A : Stores S) (U : Config G f) (V : Config G c) (k : S.Choices)
    (x e d W : ℝ) (h : Seeded A U k V x W) (he : WeakTicket T A x U k V e d) (h0 : 0≤e)
    {D : ℝ} (ht : Bid.LaneCounts T.up x (fiery G x S.patch.L) T.high D 1 S.ratio.parent) :
    core T A x V U k / 2 - 2*e*Fintype.card (Cell c) ≤ unassigned A T x U k V := by
  let Q := S.prediction U k; let X := (A.limit x)ᶜ; let Y := (A.intern x)ᶜ; let Z := (A.outs x)ᶜ
  let t := fiery G x S.patch.L; let s := temp x; let b := till x
  rw [unassigned_exterior]; unfold onWindow core
  have hv j := fun (i : Bond c) => core_origin T U V Q b t s j i
  have hl j : ‖shiftedBond T b s V Q j‖^2/2 ≤ T.workI b Q V s j := by
    apply (hv ((0, ⟨(0,1),by decide⟩) : Cell f) j).2
  have hi i (hx : i∈X) : ‖shiftedFine T b s V U i‖^2/2 ≤ T.workF b U V t s i := by
    apply (hv i (0,0)).1 (default_fine h (Finset.mem_compl.mp hx)) (default_keeps h T D ht (Finset.mem_compl.mp hx))
  have hz : ∑ i, faceBill T A x V U i^2 = ∑ i∈X, ‖shiftedFine T b s V U i‖^2 := by
    unfold X faceBill; simp only [apply_ite (· ^ (2:ℕ)),zero_pow (by norm_num : 2≠0)]
    rw [show (A.limit x)ᶜ=Finset.univ.filter (fun i => i∉ A.limit x) by ext; simp,Finset.sum_filter]; simp
    rfl
  have hy : ∑ i, bondBill T A x V Q i^2 = ∑ i∈Y, ‖shiftedBond T b s V Q i‖^2 := by
    unfold Y bondBill; simp only [apply_ite (· ^ (2:ℕ)),zero_pow (by norm_num : 2≠0)]
    rw [show (A.intern x)ᶜ=Finset.univ.filter (fun i => i∉ A.intern x) by ext; simp,Finset.sum_filter]; simp
    rfl
  change ((∑ i,faceBill _ A x _ _ i^2)+∑ i,bondBill _ A x _ Q i^2)/2-2*e*_ ≤
    (∑ i∈X,T.workF b U V t s i)+(∑ i∈Y,T.workI b Q V s i)+ (∑ i∈_ ,_)+_
  rw [hz,hy, add_div,Finset.sum_div,Finset.sum_div,sub_eq_add_neg]
  apply le_trans ?_ (le_add_of_nonneg_right (b:=∑ i∈(A.coordN x)ᶜ, T.workN b V s i) (by unfold workN; positivity))
  apply add_le_add (add_le_add (Finset.sum_le_sum hi) (Finset.sum_le_sum fun i _ => hl i))
  apply le_trans ?_ (Finset.sum_le_sum fun i (hi : i∈Z) => add_le_add (he.clipped i (Finset.mem_compl.mp hi)) (he.defect i (Finset.mem_compl.mp hi)))
  simp only [Finset.sum_const,nsmul_eq_mul]; nlinarith [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr (Finset.card_le_univ Z)) h0]

-- simple demonstration extracting the center at tight scale (needn't be stationary).
private lemma minim {I : Type} {K : Set I} {f : I → ℝ} (hK : K.Nonempty) (h : ∀ i, 0 ≤ f i)
    (ε : ℝ) (he : 0<ε) : ∃ i∈K, ∀ j∈K, f i ≤ f j+ε := by
  let S := f '' K
  have hs : S.Nonempty := hK.image f
  have hB : BddBelow S := ⟨0,by rintro _ ⟨i,hi,rfl⟩; exact h i⟩
  obtain ⟨_,⟨i,hi,rfl⟩,he⟩ := exists_lt_of_csInf_lt hs (lt_add_of_pos_right _ he)
  exact ⟨_,hi,fun j hj => he.le.trans (add_le_add_left (csInf_le hB ⟨j,hj,rfl⟩) _)⟩

private lemma identity_store {c f : Side} {S : StepData c f} (A : Stores S) : Oriented.turnStore 1 A = A := by
  have he : faces 1 f=Equiv.refl _ := by
    ext p : 1
    have hh : Face.lower p 1 (0:Site f)=p.1 := by simp [Face.lower,atFace,affine,posDir]
    have hs : p.2.rotate 1=p.2 := by
      apply Subtype.ext
      simp only [PlaqAxes.rotate,PlaqAxes.ordered,Signed.one_perm,Equiv.refl_apply]
      simp [p.2.property.le]
    change Face.send 1 0 p = _; rw [Face.send,hh, hs]; rfl
  have hb : StepData.sendBonds 1 (0:Site c)=Equiv.refl _ := by
    ext i : 1; change sendEdge 1 0 _ = i
    simp [sendEdge,affine,Step.used,posDir]
  have ht : StepData.sendSites 1 (0:Site c)=Equiv.refl _ := by
    ext i : 1; change Signed.act 1 i + 0 = i; simp
  unfold turnStore; rw [he,hb,ht]
  have h {α : Type} (F : Finset α) : F.map (Equiv.refl α).symm.toEmbedding = F := by
    ext; simp
  simp_rw [h]

set_option maxHeartbeats 600000 in
/-- Center both the single and simultaneous charges at a common near
min of JUST what needs to be controlled in unassigned; hence can use the same
center when passing to all orientations with their real weights. No need to assert
centers are gauge equivariant themselves or have local dependence. -/
lemma away (P : Teller G) (L : Side) (W : ℝ) (hw : 0<W) :
    ∃ (γ : ℝ) (l : ℝ → ℝ), 0<γ ∧ (∀ n : ℕ, Tendsto
      (fun x : ℝ => b x ^ n * y G L x*l x) atTop (𝓝 0)) ∧
    ∀ᶠ x in atTop, 0 ≤ l x ∧
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x)≤c.val → P.Funds S T →
        ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c), ∃ ξ : F.Slice G,
          ∀ (U : Config G f) (k : S.Choices), SliceSet S F U → Seeded A U k V x W → Alive S U k →
            ∀ (o : Bool),
              γ*pairCost A x U (F.drape ξ) - l x*(Fintype.card (Site c):ℝ) ≤ rest o T A x U k V := by
  obtain ⟨C,e,hC,he,Hc,hm⟩ := pair_quote P L W hw
  obtain ⟨d,hd,hl⟩ := weak_pre P
  obtain ⟨z,hz,hq,H⟩ := hl L W hw
  obtain ⟨D,hD,hP⟩ := Work.E04.answer Work.E03.answer P
  let a := 1/(4*C)
  have ha : 0<a := by unfold a; positivity
  let m : ℝ := Fintype.card PlaqAxes
  let q : ℝ := Fintype.card Signed
  have hq' : 1≤q := by unfold q; exact_mod_cast Fintype.card_pos
  have hQ : 0<q := by linarith
  let v x := e x + Real.exp (-1*till x)
  let l x := 2*m*z x+v x
  have hvl n : Tendsto (fun x : ℝ => b x ^ n * y G L x * v x) atTop (𝓝 0) := by
    have h1 := Hc n; have h2 := cutoff G L n 0 (τ:=1) one_pos
    have h := h1.add h2; rw [add_zero] at h
    exact h.congr fun x => by unfold v; ring
  refine ⟨a/q,l,by positivity,fun n => ?_,?_⟩
  · have ht := ((hq n).const_mul (2*m)).add (hvl n); rw [mul_zero, add_zero] at ht
    exact ht.congr fun x => by unfold l; ring
  filter_upwards [he,hm,hz,H,(hP L W).late] with x he hx hz hZ hT
  have he' : 0<v x := add_pos_of_nonneg_of_pos he (Real.exp_pos _)
  have hl : 0 ≤ l x := by unfold l m; positivity
  refine ⟨hl,?_⟩; intro c f S T hL hX hF F A V
  let K : Set (Config G f × S.Choices) := {u | SliceSet S F u.1 ∧ Seeded A u.1 u.2 V x W ∧ Alive S u.1 u.2}
  by_cases hK : K.Nonempty
  swap
  · refine ⟨fun _ => 1,fun U k hi hh ha => (hK ⟨(U,k),hi,hh,ha⟩).elim⟩
  let N : ℝ := Fintype.card (Site c)
  have hN : 0<N := by unfold N; exact_mod_cast Fintype.card_pos
  have hA (F : Forest S.ratio) (A : Stores S) (V U k) (hi : SliceSet S F U) (he : Seeded A U k V x W)
      (hh : Alive S U k) : core T A x V U k / 2 - 2*z x*m*N ≤ unassigned A T x U k V := by
    obtain ⟨hk,-⟩ := hT c f S hL hX T hF F A U k V hi (he.plot hh); rw [← hL] at hk
    apply le_trans ?_ (acts_origin T A U V k x (z x) d W he (hZ _ _ _ _ hL hX hF _ _ _ _ _ hi he hh) hz hk)
    rw [show Fintype.card (Cell c) = _ from Fintype.card_prod (Site c) PlaqAxes]; unfold N m; push_cast; ring_nf; rfl
  let θ (u : Config G f × S.Choices) := core T A x V u.1 u.2
  obtain ⟨⟨U',k'⟩,⟨ha1,ha2,ha3⟩,hJ⟩ := minim hK (f:=θ) (fun _ => core_nn ..) (v x*N) (by positivity)
  obtain ⟨ξ,hξ,-⟩ := (slice_drape F _).mp ha1
  change F.drape ξ=U' at hξ
  refine ⟨ξ,fun U k hi he0 ha0 o => ?_⟩
  let Y := pairCost A x U U'
  let E := 2*z x*m*N
  have hh := hx _ _ _ T hL hX hF F A U U' k k' V hi ha1 he0 ha2 ha0 ha3
  have hk := hJ (U,k) (show (U,k)∈K from ⟨hi,he0,ha0⟩)
  have hp : a*Y-v x*N ≤ core T A x V U k/2 := by
    apply le_of_mul_le_mul_left (a:=4*C) _ (by positivity)
    rw [mul_sub,← mul_assoc (4*C) a Y,show 4*C*a=1 by unfold a; field_simp,one_mul]
    change Y ≤ C*(_+_+e x*N) at hh
    change core T A x V U' k' ≤ core T A x V U k + v x*N at hk
    have ht : e x ≤ v x := le_add_of_nonneg_right (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left hk hC.le,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hC.le) hN.le,mul_nonneg (mul_nonneg hC.le he'.le) hN.le]
  rw [hξ]; change a/q*Y-l x*N ≤ _
  cases o with
  | false =>
    unfold rest; simp only [Bool.false_eq_true, ↓reduceIte]
    apply le_trans ?_ (hA F A V U k hi he0 ha0)
    have hh := mul_le_mul_of_nonneg_right (div_le_self ha.le hq') (pairCost_nn A x U U')
    unfold l; linarith only [hp,hh, mul_comm m (z x)]
  | true =>
    have hB := funds_branch hF
    let R (s : Signed) := core T (turnStore s A) x (pull s 0 V) (pull s 0 U) (choice s k)
    let f s := unassigned (turnStore s A) T x (pull s 0 U) (choice s k) (pull s 0 V)
    have hv (s : Signed) : R s / 2 - E ≤ f s := hA (turnForest s F) _ _ _ _
      (turn_sliced s _ _ hi) (pull_seeded s hB he0)
        (by unfold Alive; rw [(carry s hB k U).1]; exact ha0)
    have he := average_one (fun s => R s / 2) (fun s => div_nonneg (core_nn ..) (by norm_num))
    have hr : R 1=core T A x V U k := by
      unfold R; rw [identity_store,pull_id,pull_id]
      have ha := (carry (1:Signed) hB k U).2; rw [pull_id,pull_id] at ha
      unfold core; rw [ha]
    rw [show rest true T A x U k V = averaged f from rfl]
    apply le_trans ?_ (av_mono hv)
    rw [show averaged (fun s => R s / 2 - E) = _ from av_sub _ (fun _ => E), av_const]
    apply le_trans ?_ (sub_le_sub_right he _)
    rw [hr]; change _ ≤ q⁻¹*_-_
    apply (le_of_mul_le_mul_left (a:=q) ?_ hQ)
    unfold l E; field_simp
    nlinarith [mul_le_mul_of_nonneg_right hq' (show 0 ≤ v x*N by positivity),mul_comm m (z x)]
end YM.SectorNext.Remainder.Center
