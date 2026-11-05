import YM.Next.STATIONARY.Shape.Vertex



set_option autoImplicit false
/-!
# True-length and leading-order test on *input* loop path families

On actual Bounds including normalized moments. Use even on harmonic and
wrapped site periods. Unmasked here. -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Asymptotics Laurent Lattice Exterior Bloch Precision RG Wilson
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {m : Side} {σ A Λ : ℝ}

section group
variable (R : PathData G) (b : CurRun 2) (i : Ink G 2)
def coreRate : ℕ → ℝ := R.loop_coeff (plaqEquiv.symm ∘ b) i

def wedgePlace (n : ℕ) : Cover := ((R.loop n).leg 1).offset-((R.loop n).leg 0).offset

def basin (x : Cover) := ∑' n : wedgePlace R ⁻¹' {x}, coreRate R b i n
lemma core_zero (n : ℕ) : coreRate R b i n=
    if b=fun j => plaquette (((R.loop n).leg j).plaq) then (R.loop n).coeff i else 0 := by
  unfold coreRate PathData.loop_coeff
  split_ifs with h he he <;> try rfl
  · apply False.elim (he _); funext k; apply plaqEquiv.symm.injective; rw [show (((R.loop n).leg k).plaq)=_ from congr_fun h k]; exact (plaqEquiv.symm_apply_apply _).symm
  exfalso; apply h; funext k; simp only [Function.comp_apply, he]; exact (plaqEquiv.symm_apply_apply _).symm
lemma wedge_tax (n : ℕ) : size (wedgePlace R n) ≤ (R.loop n).length := by
  let f i := (R.loop n).leg i
  have he (a : Slot) : size a.offset ≤ a.length := by
    have hh := fees_end a.walk (0:Cover)
    apply (hh.trans ?_); simp [Laurent.size,Slot.length]
  unfold wedgePlace; rw [sub_eq_add_neg]
  apply (size_add ..).trans; rw [size_neg, Atom.length, Fin.sum_univ_two,Nat.add_comm ((R.loop n).leg 0).length]; exact Nat.add_le_add (he _) (he _)

variable {p : Clip} (h : R.Bounds p σ A Λ)
include h
private lemma spirit (M : ℕ) : ‖coreRate R b i M‖ * Real.exp (σ * size (wedgePlace R M))≤ (R.loop M).budget σ := by
  rw [core_zero,Real.norm_eq_abs]; unfold Atom.budget; split
  next hw =>
    have hp := h.width
    apply mul_le_mul (b:= (R.loop M).magnitude) (single_le_sum (fun a _ => abs_nonneg ((R.loop M).coeff a)) (mem_univ i)) _
      (Real.exp_pos _).le (by unfold Atom.magnitude; positivity)
    gcongr
    exact wedge_tax R _
  simp only [abs_zero,zero_mul]; unfold Atom.magnitude; positivity

lemma fillTank : Width σ Λ (basin R b i) := by
  let F := coreRate R b i
  let f (n : ℕ) := ‖F n‖*Real.exp (σ*size (wedgePlace R n))
  have he : SumBudget f Λ := Work.F08.budget_minor h.two (fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (spirit R _ _ h)
  have hs := he.2.1.hasSum.tsum_fiberwise (wedgePlace R)
  unfold Width; refine Work.F08.budget_minor (show SumBudget _ Λ from ⟨fun i => tsum_nonneg fun _ => he.1 _,hs.summable, hs.tsum_eq.trans_le he.2.2⟩)
    (fun _ => by positivity) ?_
  intro j
  simp_rw [f,show ∀ (u : wedgePlace R ⁻¹' {j}), wedgePlace R u=j from fun i => i.property, tsum_mul_right,mul_comm _ ‖basin _ _ _ _‖]
  exact mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm (((h.loopTerms _ i).1.subtype (wedgePlace R ⁻¹' {j})).norm)) (Real.exp_pos _).le

lemma basin_origin : Rays 2 (readable (basin R b i) ∘ axes) := by
  let f := basin R b i
  let C := coreRate R b i
  have hw : Summable C := (h.loopTerms _ i).1
  have he := fillTank R b i h
  have hy : AnalyticAt ℝ (readable (basin R b i) ∘ axes) 0 :=
    ((Firm.of_series (A:=Λ) (f:=fun x => (f x:ℂ)) (by simpa only [Width, Complex.norm_real] using he) h.width).analytic_real 0)
  have hz0 : (∑' x,f x)=0 := (hw.hasSum.tsum_fiberwise _).tsum_eq.trans (h.loop_normal (plaqEquiv.symm ∘ b) i).1
  have H (k) : (∑' n, f n * (n k:ℤ))=0 := by
    have hp := h.loopTerms (plaqEquiv.symm ∘ b) i
    have hl : Summable (fun n : ℕ => C n*(wedgePlace R n k:ℤ)) := hp.2 k
    have hz := hl.hasSum.tsum_fiberwise (wedgePlace R)
    simp_rw [show ∀ (j) (b : wedgePlace R ⁻¹' {j}), wedgePlace R b=j from fun i b => b.property, tsum_mul_right] at hz
    exact hz.tsum_eq.trans ((h.loop_normal (plaqEquiv.symm ∘ b) i).2 k)
  have hx (k : Axis) : fderiv ℝ (readable (basin R b i) ∘ axes) 0 (Pi.single k 1)=0 := by
    have ht := (vertical_moment he h.width k).2
    rw [show ∑' x, basin R b i x*_=0 from H k,Complex.ofReal_zero,zero_mul] at ht
    exact (Push.side _ hy.differentiableAt _).unique ht
  refine (rays_jet hy 2).2 fun k hk => ?_
  interval_cases k
  · ext1 v; simp [Function.comp_apply,readable,Laurent.read, ← Complex.ofReal_tsum,show (∑' x,basin R b i x)=0 from hz0]
  ext1 v; simp only [iteratedFDeriv_one_apply]; rw [show v 0=∑ i : Axis,(v 0 i) • Pi.single i (1:ℝ) by
    funext i; simp [Finset.sum_apply,Pi.single_apply,mul_ite], map_sum]; simp [hx]
end group

section fees
variable (R : PathData G)
def tendInk : Picture G 1 := fun i b p => ∑ x : CurRun 2, symbol 1 (-(axisPair p)) (x 0) (b 0) *
    symbol 1 (axisPair p) (x 1) (b 1) * readable (basin R x i) (axisPair p)

variable {p : Clip} (h : R.Bounds p σ A Λ)
include h

lemma stem (a : CurRun 2) (v : Ink G 2) (P : Momentum) (hP : star P=P) :
    HasSum (fun x : ℕ => mode P (wedgePlace R x) * ↑(coreRate R a v x)) (readable (basin R a v) P) := by
  let f x := mode P (wedgePlace R x) * ↑(coreRate R a v x)
  have ht : Summable f := by
    refine Summable.of_norm ?_
    simp only [f,norm_mul,mode_real _ _ hP,one_mul,Complex.norm_real]
    exact (h.loopTerms _ v).1.norm
  have he := ht.hasSum.tsum_fiberwise (wedgePlace R)
  simp_rw [f,show ∀ x (b : wedgePlace R ⁻¹' {x}),wedgePlace R b=x from fun _ b => b.property,
    tsum_mul_left,← Complex.ofReal_tsum] at he
  rw [show readable (basin R a v) P = ∑' i,f i from he.tsum_eq]; exact ht.hasSum

private lemma bit (x : Fin 2→Site m) (hx : ∑ i,x i=0) (i : Ink G 2) (b : Run 2) (n : ℕ) :
    enlarge (inkNote 0 (R.loop n)).toMultilinearMap (glyph x i b) =
        ∑ a : CurRun 2, symbol 1 (-mon (x 1)) (a 0) (b 0) *
          symbol 1 (mon (x 1)) (a 1) (b 1) * (mode (mon (x 1)) (wedgePlace R n)*(coreRate R a i n:ℂ)) := by
  let q := fun i : Fin 2 => plaquette (((R.loop n).leg i).plaq)
  simp_rw [core_zero]; change _=∑ a : CurRun 2, _*(_*((if a=q then _ else 0:ℝ):ℂ))
  rw [Finset.sum_eq_single q]; rotate_left
  · intro a _ ha; simp [ha]
  · simp
  simp only [if_true]
  have he := ties hx 0
  have hs : plotted (outphase x) 0= -mon (x 1) := by simp [plotted,missing]; rfl
  rw [hs] at he
  have H x' := he.exp x'
  rw [ink_atom_wave (t:=1), show (∏ j : Fin (1+1), cell (x j) _ * symbol _ _ _ _) = _ from Fin.prod_univ_two _]; simp only [ add_zero,cell_wrap,
    ← H, ← rolls_symbol he,mode_inverse,wedgePlace,sub_eq_add_neg,mode_shift,mode_opposite]
  unfold q; ring

lemma recoup_core (x : Fin 2→Site m) (i b) : enlarge (volumeInk m R.loop).toMultilinearMap (glyph x i b) =
    collected (tendInk R) x i b := by
  rw [volume_wave R.loop h.width h.two, collected]; split; swap; rfl
  rename_i hx
  congr 1; unfold tendInk; rw [show axisPair (outphase x)=mon (x 1) from rfl]
  have hm (a : CurRun 2) := stem R h a i (mon (x 1)) (real_frequency _)
  let k (a : CurRun 2) := symbol 1 (-mon (x 1)) (a 0) (b 0) *symbol 1 (mon (x 1)) (a 1) (b 1)
  have ht (a : CurRun 2) := (hm a).mul_left (k a)
  simp_rw [bit R h x hx]
  exact (hasSum_sum (fun i _ => ht i)).tsum_eq

def inheritRate (σ : ℝ) := (Fintype.card (CurRun 2):ℝ) * (4*(Real.exp σ + 1))^2
lemma ink_exports (i : Ink G 2) b : Firm σ (Λ*inheritRate σ) (tendInk R i b) ∧ Rays 4 ((tendInk R i b) ∘ axes) := by
  let d := 4*(Real.exp σ+1)
  have he (a) := fillTank R a i h
  have hA x : Firm σ Λ (fun p => readable (basin R x i) (axisPair p)) := by
    exact pair_firm ((Firm.of_series (f:=fun y => (basin R x i y:ℂ)) (by simpa only [Width,Complex.norm_real] using he x) h.width))
  have hP a b : Firm σ d (fun p : Momentum => symbol 1 p a b) := strip_symbol (Function.Embedding.refl Axis) h.width a b
  constructor
  · unfold tendInk; convert Firm.sum univ _ _ h.width (fun (x : CurRun 2) _ => (((pair_firm (anti_ancestral (hP (x 0) (b 0)))).mul
      (pair_firm (hP (x 1) (b 1)))).mul (hA x))) using 1
    unfold inheritRate; simp; unfold d; ring
  unfold tendInk Function.comp; apply rays_total; intro x
  have hp : Rays 1 (fun p => symbol 1 (-axisPair (axes p)) (x 0) (b 0)) := by
    intro p; have ht := ray_symbol (Embedding.refl Axis) (x 0) (b 0) (-(p ∘ stick 0))
    simp_rw [smul_neg,axes_flip] at ht; exact ht
  have hx : Rays 1 (fun p => symbol 1 (axisPair (axes p)) (x 1) (b 1)) := by
    intro p; exact ray_symbol (stick 0) (x 1) (b 1) p
  exact (hp.mul hx).mul (show Rays 2 (fun p => readable (basin R x i) (axisPair (axes p))) from fun p => basin_origin R x i h (p ∘ stick 0))
end fees
end YM.Stationary
end

/-! # Exact inheritance on all periods before pulling the stationary array. -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Asymptotics Laurent Lattice Exterior Bloch Precision RG Wilson
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {m : Side} {σ A Λ : ℝ}

section perm

def twain (d : Equiv.Perm (Fin 2)) (p : Space 1) : Space 1 := fun i => plotted p (d i.1.succ) i.2
lemma twained (d : Equiv.Perm (Fin 2)) : twain d = (fun p => p) ∨ twain d=(fun p => -p) := by
  have he (p : Space 1) : plotted p 0 = -projected (stick 0) p := by simp [plotted,missing]; rfl
  have h : d 1=1 ∨ d 1=0 := by omega
  rcases h with h|h
  · left; funext p ⟨j,i⟩; have hj : j=0 := Subsingleton.elim ..
    rw [twain,hj,show (0:Fin 1).succ=1 from rfl, h]; rfl
  right; funext p ⟨j,i⟩; have hj : j=0 := Subsingleton.elim ..
  rw [twain,hj,show (0:Fin 1).succ=1 from rfl,h,he]; rfl
end perm
variable (R : PathData G)

def sortedIn (d : Equiv.Perm (Fin 2)) : Picture G 1 := fun i j p => tendInk R (i ∘ d) (j ∘ d) (twain d p)
def orderedInk : Picture G 1 := fun i j p => (2:ℂ)⁻¹ * ∑ d : Equiv.Perm (Fin 2), sortedIn R d i j p

def filing : Picture G 1 := bleed (orderedInk R)
variable {p : Clip} (h : R.Bounds p σ A Λ)
include h

lemma sorted_fee (d : Equiv.Perm (Fin 2)) (i j) : Firm σ (Λ*inheritRate σ) (sortedIn R d i j) ∧ Rays 4 ((sortedIn R d i j) ∘ axes) := by
  have he := ink_exports R h (i ∘ d) (j ∘ d)
  unfold sortedIn; rcases twained d with ht|ht <;> rw [ht]
  · exact he
  refine ⟨anti_ancestral he.1,fun p => ?_⟩
  have hh := he.2 (-p)
  simp_rw [Function.comp_apply,smul_neg,axes_flip] at hh; exact hh
lemma ordered_cost (i j) : Firm σ (Λ*inheritRate σ) (orderedInk R i j) ∧ Rays 4 ((orderedInk R i j) ∘ axes) := by
  have he d := sorted_fee R h d i j
  constructor
  · unfold orderedInk
    convert (Firm.const h.width (_:ℂ)).mul (Firm.sum Finset.univ _ _ h.width (fun d _ => (he d).1)) using 1
    norm_num [Fintype.card_perm, Nat.factorial]; ring
  intro v
  exact ((rays_total (fun x => (he x).2) v).const_mul_left _)

lemma sort_record (x : Fin (1+1)→Site m) (i : Ink G 2) (b : Run 2) (d : Equiv.Perm (Fin 2)) :
    enlarge (volumeInk m R.loop).toMultilinearMap (glyph x i b ∘ d) = collected (sortedIn R d) x i b := by
  rw [show glyph x i b ∘ ⇑d=glyph (x ∘ d) (i ∘ d) (b ∘ d) from rfl,recoup_core R h]
  unfold collected sortedIn; rw [show ∑ j,(x ∘ d) j=∑ j,x j from Equiv.sum_comp d _]
  split; next hv =>
    congr 1
    have hp : rolls (outphase (x ∘ d)) (twain d (outphase x)) := rolls_keys (fun j => (ties hv (d j.succ)).symm)
    have hh := (ink_exports R h (i ∘ d) (b ∘ d)).1
    exact hp.apply hh (hh.in_range (out_real (x ∘ d)))
  rfl
lemma sort_coins : Recorded (orderedInk R) (seriesScore m R.loop) 0 := by
  apply (record_exact ..).2
  intro p i b
  rw [ink_beat m R.loop h.width h.two]; norm_num only [show (1+1:ℕ)=2 from rfl, Nat.factorial]
  simp_rw [sort_record R h]; unfold collected orderedInk; split <;> simp [mul_left_comm,Finset.mul_sum]
lemma filing_aux (i j) : Rays 4 ((filing R i j) ∘ axes) := by
  intro p
  unfold filing bleed Function.comp; refine IsBigO.const_mul_left ?_ _
  apply Asymptotics.IsBigO.sum
  intro s _; unfold rotPix; dsimp only
  let r := s.perm.symm ∘ axisEquiv.symm ∘ j
  have ht : Firm σ _ _ := firmProd Finset.univ _ _ h.width (fun k _ => reflect_firm s h.width k (r k))
  have hh := rays_zero (ht.analytic_real 0)
  exact hh.mul (rotjet s (ordered_cost R h i _).2) p

/-- Linear budget in input norm. External kernel already vanishes to
order four; after evaluation on the A columns have to propagate this
order even on high parts. -/
theorem filing_ready : (∀ i j, Firm σ (Λ*(reflectBill 1 σ*inheritRate σ)) (filing R i j) ∧ Rays 4 ((filing R i j) ∘ axes)) ∧ ∀ m : Side, Recorded (filing R) (turnSeries (m:=m) R.loop) 0 := by
  refine ⟨fun i j => ⟨?_,filing_aux R h _ _⟩,fun m => ?_⟩
  · rw [mul_left_comm]; exact bleed_cap h.width (fun i j => (ordered_cost R h i j).1) _ _
  rw [funext (turns_frame R.loop)]; exact bleed_record (score_analytic m R.loop h.width h.two) (fun i j => (ordered_cost R h i j).1) (sort_coins R h)
end YM.Stationary
end

/-!
# Launch: the *actual* Wilson jet at the top of every ancestry
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics Metric
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {m : Side} {σ A R Λ : ℝ} {n t : ℕ}

lemma strain (p : Clip) (X : PathData G) (h : X.Bounds p σ A Λ) : Pointwise (intended p X (m:=m)) := by
  have he := fun i => h.invariant i
  rw [intent]
  exact ((stain_knit X p h).add (stain_ink _ h.width h.three (fun i => (he i).2.1))).add
    (stain_ink _ h.width h.four (fun i => (he i).2.2))

lemma matched {p q : fieldDir G m 1 → ℝ} {n : ℕ} (hp : AnalyticAt ℝ (p ∘ (arm G m 1)) 0) (hq : AnalyticAt ℝ (q ∘ (arm G m 1)) 0) (h : Rays n ((p ∘ (arm G m 1))-(q ∘ (arm G m 1)))) (i : ℕ) (he : i<n) : SameJet i p q := by
  have heq (F : fieldDir G m 1 → ℝ) (ht : AnalyticAt ℝ (F ∘ arm G m 1) 0) : ContDiffAt ℝ ω F 0 := by
    have hh := (show AnalyticAt ℝ (F ∘ arm G m 1) ((arm G m 1).symm 0) by rw [map_zero]; exact ht).comp ((arm G m 1).symm.analyticAt 0)
    simpa only [Function.comp_def, (arm G m 1).apply_symm_apply] using hh.contDiffAt (n:=ω)
  have hh := (rays_jet (hp.sub hq) n).1 h i he
  rw [iteratedFDeriv_sub_apply hp.contDiffAt hq.contDiffAt] at hh
  exact ⟨heq p hp, heq q hq, inverts G _ p q _ (heq p hp) (heq q hq) (sub_eq_zero.mp hh)⟩

lemma freeLoop {B : Bed} (X : PathData G) (h : X.loop=(blank B G).loop) (i) : (X.loop i).coeff=0 := by rw [h]; exact blank_loop ..

/-- Builds the top path and **all** its periodic comparisons with the Wilson
energy required by `peak`. Λ arbitrary for the stamp; period family cofinal
as used by any Gentle schedule. Row bank fixed by `A` and independent of cost
of the nonlinear corrections. Requires genuine data on the input Bed for every
large-volume tester.
-/
theorem launch (G : Gauge) (σ₀ A Z : ℝ) (hσ : 0 < σ₀) (hz : 0≤Z) :
    ∃ σ C : ℝ, 0 < σ ∧ σ≤σ₀ ∧ 0≤C ∧
     ∀ m : ℕ→Side, Tendsto (fun i => (m i).val) atTop atTop →
      ∀ (p : Clip) (B : Bed) (a b : ℝ), p.direct ≤ Z → B.roots.strip σ₀ A → (∀ i : Side, Floor B p i a b) →
        (∀ i, Bid.Sworn B (m i) G) → (∀ i, B.diagonal.acts (m i)=1) →
         ∃ Q : PathData G, Q.row=rowPath B ∧ Attached B Q ∧
          (∀ i, (Q.loop i).coeff=0) ∧ (∀ τ k Λ, 0<τ → τ≤σ → C≤k → rowPrice σ₀ A ≤ k → 0≤Λ → Q.Bounds p τ k Λ) ∧
          ∀ i j, j ≤ 4 → SameJet j (fun x => mainTerm p Q (represent (x:fieldDir G (m i) 1))) (fun x => Wilson.energy (represent x)) := by
  obtain ⟨h,C,yC,L,hL,Y⟩ := Wilson_stream G 2
  obtain ⟨w,B,hB,V,hV,Z'⟩ := Wilson_stream G 3
  let M := 1+C+B
  have hy : 1≤M := le_add_of_nonneg_right hB |>.trans' (le_add_of_nonneg_right yC)
  obtain ⟨τ,K,hτ,_,hK,H⟩ := assembly G 1 σ₀ A Z one_pos hσ hz
  refine ⟨min τ σ₀,M*K, lt_min hτ hσ,min_le_right .., mul_nonneg (le_trans zero_le_one hy) hK,fun m hm p D a b hp hD hF hz hx => ?_⟩
  have hl i : Rays 3 (WilsonQ G (m i) - inputSeries p (blank D G)) := top_Wilson (blank_cap hσ hD (hF 1) (Ω:=A) le_rfl (Λ:=0) le_rfl) (rows_layout rfl) (hF _) (hz i) (hx i)
  let E i := WilsonQ G (m i)
  have he : HasRecord E 1 C 2 := ⟨L,hL,fun i => Y _⟩
  have hu : HasRecord E 1 B 3 := ⟨V,hV,fun i => Z' _⟩
  obtain ⟨X,O,HA,Hb,Hi⟩ := H m hm D p a b hD (hF 1) hp E (fun i => Wilson_witness) hl _ hy (he.mono one_pos le_rfl (by unfold M; linarith)) (hu.mono one_pos le_rfl (by unfold M; linarith))
  let Q := emitBase G D (blank D G).loop X O
  have hq : Q.loop=(blank D G).loop := rfl
  have HH s k Λ (hh : 0<s) (hs : s ≤ min τ σ₀) (he : M*K ≤ k) (hb : rowPrice σ₀ A ≤ k) (hx : 0 ≤ Λ) : Q.Bounds p s k Λ := by
    let R := blank D G
    have h1 := HA.mono (hs.trans (min_le_left ..)) he; have h2 := Hb.mono (hs.trans (min_le_left ..)) he
    -- retarget price via exp4 monotonic using A>0 from actual rows
    have ht : 0≤A := by
      let P : PlaqAxes := ⟨(0,1),by decide⟩
      have hm := hD (plaquette P) (plaquette P)
      exact (tsum_nonneg hm.1).trans hm.2.2
    have hS : s≤σ₀ := hs.trans (min_le_right ..)
    have hR : R.Bounds p s k Λ := blank_cap hh (fun i j => (hD i j).mono hS le_rfl) (hF 1) (le_trans (show rowPrice s A ≤ rowPrice σ₀ A by unfold rowPrice; gcongr) hb) hx
    exact ⟨hh,hR.rows,hR.two,h1.1,h2.1,fun i => ⟨(hR.invariant i).1,HA.2 _, Hb.2 _⟩,hR.symTerms,hR.metric,hR.loopTerms,hR.loop_normal⟩
  have ht := HH (min τ σ₀) (max (M*K) (rowPrice σ₀ A)) 0 (lt_min hτ hσ) le_rfl (le_max_left ..) (le_max_right ..) le_rfl
  refine ⟨Q,rfl,rows_layout rfl,freeLoop Q hq,HH,fun i j hj => ?_⟩
  obtain ⟨h1,h2,h3⟩ := matched (p:=fun x : fieldDir G (m i) 1 => Wilson.energy (represent x)) (q:=fun x => mainTerm p Q (represent x)) (h _) (strain _ Q ht).analytic (Hi ((blank D G).loop) i) j (by omega)
  exact ⟨h2,h1,h3.symm⟩
end YM.Stationary
end

/-!
# Assemble BEAT powers from classical soft kernels. Arbitrary PathData (not
assuming any fixed root path choices), coupons supplied at τ. Gain from
comparison with Wilson, using symmetry of H on one-cochain channel
and the zeroth jet H2-cost. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {t n u : ℕ} {c f L : Side} {σ A C D w η : ℝ} {p : Clip} {R : PathData G}

abbrev ageCore (p : Clip) (R : PathData G) (m : ℕ→ Side) (i) := inputSeries p R (m:=m i)
def cureCore (R : PathData G) (m : ℕ→Side) (i) := turnSeries R.cubic (m:=m i)+turnSeries R.quartic
lemma intent_bound (p : Clip) (R : PathData G) (m : ℕ → Side) : (fun i=> intended p R (m:=m i))=ageCore p R m + cureCore R m := by
  funext i; rw [Pi.add_apply,intent]; unfold ageCore cureCore; abel
lemma cures (m : ℕ → Side) (h : R.Bounds p σ C D) (i) : Pointwise (cureCore R m i) ∧ Rays 3 (cureCore R m i) := by
  exact ⟨(stain_ink _ h.width h.three (fun i => (h.invariant i).2.1)).add (stain_ink _ h.width h.four (fun i => (h.invariant i).2.2)),(turns_low R.cubic h.width h.three).add ((turns_low R.quartic h.width h.four).weaker (by decide : 3≤4))⟩

section m
variable {m : ℕ → Side} {U V : ∀ i,Link G (m i)→ℝ}
lemma Drinkable.thins (h : Drinkable t m U n σ A) (hw : 0<η) (he : η≤σ) (hc : A≤C) (hk : u≤n) : Drinkable t m U u η C := by
  obtain ⟨Q,h,H⟩ := h; exact ⟨Q,h,fun i j => ⟨(H i j).1.mono hw he hc,(H i j).2.weaker hk⟩⟩
lemma Drinkable.more (h : Drinkable t m U n σ A) (hv : Drinkable t m V n σ C) (hf : ∀ i,AnalyticAt ℝ (U i) 0) (hh : ∀ i,AnalyticAt ℝ (V i) 0) : Drinkable t m (U+V) n σ (A+C) := by
  obtain ⟨Q,h,H⟩ := h; obtain ⟨D,hD,HD⟩ := hv
  exact ⟨Q+D,fun i => (h i).both (hf i) (hh i) (hD i),fun i j => ⟨(H i j).1.add (HD i j).1,(H i j).2.add (HD i j).2⟩⟩
lemma wannabe (_ : ∀ i,AnalyticAt ℝ (U i) 0) (hv : ∀ i,iteratedFDeriv ℝ (t+1) (U i) 0=0) (hs : 0<σ) (hc : 0≤C) : Drinkable t m U u σ C := by
  refine ⟨0,fun i p a b=> ?_,fun i j => ⟨(Firm.zero hs).mono hs le_rfl hc,fun p => isBigO_zero ..⟩⟩
  unfold noteAt beat collected; rw [hv i, enlarge]; split <;> simp [recording_apply]


lemma pact {B : Bed} {x y : ℝ} (hp : R.Bounds p σ C D) (he : Attached B R) (hf : ∀ i, Floor B p (m i) x y) (hx : ∀ i,Bid.Sworn B (m i) G) (i : ℕ) : fderiv ℝ (intended p R) (0:Link G (m i))=0 := by
  have hL := intent_bound p R m
  rw [show intended p R (m:=_) = ageCore p R m i+cureCore R m i from congr_fun hL i]
  have ha := (stain_knit R p hp (m:=m i)).analytic
  obtain ⟨hV,hW⟩ := cures m hp i
  rw [fderiv_add ha.differentiableAt hV.analytic.differentiableAt,(show fderiv ℝ (ageCore p R m i) (0:Link G (m i))=0 from (low_columns hp he (hf i) (hx i)).2.1),zero_add]
  have he := (rays_jet hV.analytic 3).1 hW 1 (by decide)
  ext1 u; have hv := DFunLike.congr_fun he ![u]; simpa [iteratedFDeriv_one_apply] using hv
end m

theorem veneer (G : Gauge) (σ : ℝ) (hs : 0<σ) :
    ∃ η B, 0<η ∧ 0≤B ∧ ∀ (m : ℕ→Side), Tendsto (fun i => (m i).val) atTop atTop →
      ∀ (p : Clip) (R : PathData G) (A C : ℝ), 0≤ A → R.Bounds p σ A C →
        ∀ i, i>0 → i≤3 → Drinkable i m (cureCore R m) (4-i) η (A*B) := by
  obtain ⟨x,K,hx,hk,E⟩ := extra_curves G σ hs; refine ⟨x,K,hx,hk,fun m hm p R A C hA hY i he hi => ?_⟩
  obtain ⟨L,M,hy,hv,H⟩ := E m hm R.cubic R.quartic A hA ⟨hY.three,fun i=> (hY.invariant i).2.1⟩ ⟨hY.four,fun i=> (hY.invariant i).2.2⟩
  interval_cases i
  · exact wannabe (fun i=> (cures m hY i).1.analytic) (fun i=> (rays_jet (cures m hY i).1.analytic 3).1 (cures m hY i).2 (1+1) (by decide)) hx (mul_nonneg hA hk)
  · exact ⟨L,fun i=> (H i).1, hy⟩
  exact ⟨M,fun i=> (H i).2, hv⟩

-- Weighted cost of the propagated vacuum step on an ARBITRARY PathData
-- with Bounds. Compare Wilson before any gauge charts. Uses fder=0 from
-- symmetries of the local unmasked terms.
lemma greyson (G : Gauge) (σ ε C Z τ A : ℝ) (hs : 0<σ) (hC : 0≤C) (hZ : 0≤Z) (hτ : 0<τ) (hA : 0≤A) : ∃ s M,0<s ∧ 0≤M ∧ ∀ (m : ℕ→ Side), Tendsto (fun i => (m i).val) atTop atTop → ∀ (B : Bed) (p : Clip) (R : PathData G) Λ, R.Bounds p τ A Λ → Attached B R → B.metric.strip σ C → p.direct ≤ Z → (∀ n,Floor B p n ε C) → (∀ i,Bid.Sworn B (m i) G) →
    ∀ i, i>0 → i≤3 → Drinkable i m (fun i => intended (m:=m i) p R-WilsonQ G (m i)) (4-i) s M := by
  obtain ⟨w,P,hp,hq,L⟩ := column_price G 2 A Z hτ hZ
  obtain ⟨v,T,hv,hk,U⟩ := column_price G 3 A Z hτ hZ
  obtain ⟨hk',x,hx,H,h,H₀⟩ := Wilson_stream G 2
  obtain ⟨hq',y,hy,V,hV,H₁⟩ := Wilson_stream G 3
  obtain ⟨u,W,hu,hW,X⟩ := veneer G τ hτ
  let d := min w v; let e := min σ 1
  let a := min d e
  have hd : 0<d := lt_min hp hv
  have he : 0<e := lt_min hs zero_lt_one
  have ha : 0<a := lt_min hd he
  let b := bedCharge σ C+ bedCharge σ 1
  let g := b+P+T+x+y
  have hb : 0≤ b := add_nonneg (bedCharge_nonneg hC) (bedCharge_nonneg zero_le_one)
  have hg : 0≤g := by unfold g; positivity
  let s := min a u
  have ht : 0<s := lt_min ha hu
  refine ⟨s,g+A*W,ht,add_nonneg hg (mul_nonneg hA hW),fun m hm B p R Λ hR hB hw hY hh hj k hN hM => ?_⟩
  -- f=raw minus Wilson (Log not Dough)
  have hk : BankRows R τ A := hR.rows
  obtain ⟨hL,l,hl,l'⟩ := L p R _ _ _ hY hR hk
  obtain ⟨hT,j,hj',j'⟩ := U p R _ _ _ hY hR hk
  let F i := inputSeries (m:=m i) p R-WilsonQ G (m i)
  have ht' i : Pointwise (inputSeries p R (m:=m i)) := stain_knit R p hR
  have hf i : Pointwise (F i) := (ht' i).sub Wilson_witness
  have hu₀ := (whites_on_K hR hB hw hs (fun i=> hh (m i)) hj (F:=ageCore p R m) (fun _=>rfl)).2
  have he (i j') : Firm a g ((l-H) i j') := (((hl i j').mono ha ((min_le_left ..).trans (min_le_left ..)) le_rfl).sub ((h i j').mono ha ((min_le_right ..).trans (min_le_right ..)) le_rfl)).mono ha le_rfl (by unfold g; linarith)
  have hE (i k') : Firm a g ((j-V) i k') := (((hj' i k').mono ha ((min_le_left ..).trans (min_le_right ..)) le_rfl).sub ((hV i k').mono ha ((min_le_right ..).trans (min_le_right ..)) le_rfl)).mono ha le_rfl (by unfold g; linarith)
  have hr i : Recorded (l-H) (F i) 0 := (l' (m i)).less (ht' i).analytic (hk' (m i)) (H₀ (m i))
  have hr' i : Recorded (j-V) (F i) 0 := (j' (m i)).less (ht' i).analytic (hq' (m i)) (H₁ (m i))
  obtain ⟨hQ,hQ'⟩ := pure_grey hm hf (fun i => (show fderiv ℝ (F i) 0=0 by unfold F; rw [fderiv_sub (ht' i).analytic.differentiableAt (hk' _).differentiableAt,(low_columns hR hB (hh (m i)) (hj i)).2.1,(outright G _).2.1,sub_self])) hu₀ (l-H) (j-V) he hr hE hr'
  have h₀ (k) (hN : 0<k) (hM : k≤3) : Drinkable k m F (4-k) a g := by
    interval_cases k
    · refine ⟨slots B.metric G-slots leader G,fun i=> (according (B.metric.rights _ _ hw hs.le) (low_columns hR hB (hh (m i)) (hj i)).2.2).less (ht' i).analytic Wilson_witness.analytic (outright G (m i)).2.2,fun i j => ⟨?_,slots_gain hs hw (hh 1).starts i j⟩⟩
      apply ((slots_cost hs hw i j).sub (slots_cost hs (leader_pay σ) i j)).mono ha ((min_le_right ..).trans (min_le_left ..)); show b≤g; unfold g; linarith
    · exact ⟨_,hr,fun i j=> ⟨he i j,hQ i j⟩ ⟩
    exact ⟨_,hr',fun i j => ⟨hE i j,hQ' i j⟩ ⟩
  have hW i : intended (m:=m i) p R-WilsonQ G (m i)=(F+cureCore R m) i := by
    rw [show intended (m:=m i) p R=ageCore p R m i+cureCore R m i from congr_fun (intent_bound p R m) i]; change inputSeries _ _+_ - _ = (inputSeries _ _-_)+_; abel
  rw [show (fun i=> intended (m:=m i) p R-WilsonQ G (m i))=F+cureCore R m from funext hW]; exact ((h₀ k hN hM).thins ht (min_le_left ..) le_rfl le_rfl).more ((X m hm p R A Λ hA hR k hN hM).thins ht (min_le_right ..) le_rfl le_rfl) (fun i=> (hf i).analytic) (fun i=> (cures m hR i).1.analytic)

-- Wilson's head alone can be charged independently of the tick paths.
-- Order of notation: joint `t+1` waves, derivative divided by (t+1)!,
-- explicit analytic continuation.
lemma whiteWilson (G : Gauge) : ∃ B:ℝ,0≤B ∧ ∀ (m : ℕ→Side), Tendsto (fun i=> (m i).val) atTop atTop → ∀ k, k>0 → k≤3 → Drinkable k m (fun i => WilsonQ G (m i)) (3-k) 1 B := by
  obtain ⟨hV,Y,hY,F,h,H⟩ := Wilson_stream G 2
  obtain ⟨_,Z,hZ,K,hK,hU⟩ := Wilson_stream G 3
  let D := bedCharge 1 1
  have h₁ : (0:ℝ)<1 := zero_lt_one
  have hd : 0≤D := bedCharge_nonneg (le_of_lt h₁)
  refine ⟨D+Y+Z,by positivity,fun m hm k hk he => ?_⟩
  let V i := WilsonQ G (m i)
  have hx : Drinkable 1 m V 2 1 D := ⟨slots leader G,fun i=> (outright G _).2.2,fun i j=> ⟨slots_cost h₁ (leader_pay 1) i j,bed_rays h₁ (leader_pay 1) i j⟩⟩
  interval_cases k
  · exact hx.thins h₁ le_rfl (by linarith) (by decide)
  · have hf : LawfulSum 2 m V 1 := by
      rcases hx with ⟨x,y,Y⟩; exact ⟨x,⟨1,D,fun i j=> (Y i j).1⟩,y,fun i j=> (Y i j).2⟩
    exact ⟨F,fun i=>H _,fun i j=> ⟨(h i j).mono h₁ le_rfl (by linarith),pure_white hm (fun i=> Wilson_witness) (fun i=> (outright G _).2.1) hf _ h (fun _=>H _) i j⟩⟩
  exact ⟨K,fun i=> hU _,fun i j=> ⟨(hK i j).mono h₁ le_rfl (by linarith),rays_zero ((hK i j).analytic_real 0)⟩⟩

end YM.Stationary
end
