import YM.Planned.PRIMARY_INTEGRAL_295.Savings
import YM.Planned.PRIMARY_INTEGRAL_295.Tones


/-!
# Cost of the stationary row's stencil direction in each embedded layer

Direction may come from b (actual normalized coarse data after chart
selection) or every derivative of b. Need them all genuinely paid.
Directions of layers are used in mixed combinations; this proof does
not let different journey increment orders use different coarse fields in
claiming a Leibniz expansion!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Units
open Function Filter Set Metric Labels Lattice RG Place Carrier Source Bloch Precision Next.Free
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {d n j t : ℕ} {S : Finset Cover}

-- Uses SNOC enumeration. a=d is the residual, cost L^(-d-1).
def Rolls (S : Finset Cover) (d : ℕ) (w : Dev S G) (u C : ℝ) : Prop :=
    0≤C ∧ ∃ g : Fin (d+1) → Dev S G, w = ∑ r, g r ∧
      (∀ r, ‖g r‖ ≤ C*u^(r.val+1)) ∧ (∀ r : Fin d, ∃ f : Potential G, f∈ rangeLt (Axis→G.Color) (r.val+1) ∧ g r.castSucc = ping S f)

lemma Rolls.normed {w : Dev S G} {u C : ℝ} (h : Rolls S d w u C) (hu : u∈Icc 0 1) : ‖w‖ ≤ (d+1:ℕ)*C*u := by
  obtain ⟨hC,g,hg,h,_⟩:=h
  have he (i) := (h i).trans (mul_le_mul_of_nonneg_left (show u^(i.val+1)≤u from by simpa using pow_le_pow_of_le_one hu.1 hu.2 (Nat.succ_le_succ (Nat.zero_le i.val))) hC)
  rw [hg]; apply (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=>he i)).trans_eq ?_)
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin,mul_assoc]

-- all registered L simultaneously: support payment in C.
def inView (S : Finset Cover) (v : Window G.Color) : Dev S G := fun x=> v (first x).val (beam x)

lemma takeRow (S : Finset Cover) (d r : ℕ) (hr : d≤r) (hd : d≤ j-2) (k : ℝ)
    (hk : 0<k) (hj : 4≤j) (ht : 4≤t) : ∃ C : ℝ, 1≤C ∧ ∀ (P : Flight j t) (f : Window G.Color) (M : ℝ),
    Carries f r M → Rolls S d (inView S (applyLine (linesOf P k) f)) (unitStep P.L) (C*M) := by
  classical
  obtain ⟨C,hC,H⟩:=Trellis.saves G.Color k hk hj ht r d hr hd
  let q (x : Spot S):=liftCost r (first x).val
  let K := 1+∑ x,q x
  have hq (x : Spot S) : 0≤q x := liftCost_pos ..
  have hK : 1≤K := le_add_of_nonneg_right (Finset.sum_nonneg (fun x _=> hq x))
  have ht' (x : Spot S) : q x ≤ K := (Finset.single_le_sum (fun i _ => hq i) (Finset.mem_univ x)).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨C*K,one_le_mul_of_one_le_of_one_le hC hK,fun P f M hM=> ?_⟩
  let g := applyLine (linesOf P k) f
  let e (i : Fin d) := Trellis.sector i.val g
  let w := inView S (Trellis.surplus g d)
  have hp:=hM.1; let u:=unitStep P.L; have hu:=unitStep_pos P.L
  obtain ⟨hl,hg⟩:= H P f M hM
  let A i := ping S (e i)
  refine ⟨by positivity, Fin.snoc A w, ?_, ?_, ?_⟩
  · rw [Fin.sum_univ_castSucc]; simp only [Fin.snoc_castSucc,Fin.snoc_last]; ext1 x
    change g _ _ = (∑ i,A i) x + Trellis.surplus g d _ _
    unfold Trellis.surplus Trellis.fitting; simp only [Finset.sum_apply,Pi.sub_apply]
    rw [← Fin.sum_univ_eq_sum_range]; unfold A
    exact (add_sub_cancel _ _).symm
  · intro i
    refine Fin.lastCases ?_ (fun i=> ?_) i
    · simp only [Fin.snoc_last,Fin.val_last]; refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun x=> ?_
      let y := (first x).val
      have h' : ‖w x‖ ≤ C*M*u^(d+1)*q x := (norm_le_pi_norm (Trellis.surplus g d y) (beam x)).trans (hg y)
      apply h'.trans
      refine (mul_le_mul_of_nonneg_left (ht' x) (by unfold u; positivity)).trans_eq ?_; unfold u; ring
    simp only [Fin.snoc_castSucc,Fin.val_castSucc]; refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun x=> ?_
    let y := seat (first x).val; let z := i.val
    have he' : ‖A i x‖ ≤ C*M*u^(z+1)*(1+‖y‖)^z := (norm_le_pi_norm (e i y) (beam x)).trans ((hl z i.isLt).2 y)
    have hz : (1+‖y‖)^z ≤ q x := (pow_le_pow_right₀ (show 1≤1+‖y‖ by simp) (show z≤r from i.isLt.le.trans hr)).trans
      (pow_le_pow_left₀ (by positivity) (add_le_add_right (shade_seat _) _) r)
    apply he'.trans
    refine (mul_le_mul_of_nonneg_left (hz.trans (ht' _)) (by unfold u; positivity)).trans_eq ?_; unfold u; ring
  intro i; exact ⟨e i,(hl _ i.isLt).1,Fin.snoc_castSucc ..⟩

section
variable {T : Labels.Frame G d} (A : Hol G) (B : SectionData T) (h : B.Sound A) (b : Bid.pop B) (i : T.Index)
variable {u t M : ℝ}

-- expansion at 0, order r preassigned.
set_option maxHeartbeats 400000 in
include h in
private lemma at_launch (r : ℕ) (v : Fin r → Dev B.stencil G) (hu : u∈Icc 0 1) (hM : 0 ≤ M)
    (hV : ∀ i, Rolls B.stencil d (v i) u M) (C : ℝ) (hC : 0≤C)
    (hh : ‖iteratedFDeriv ℝ r (Tones.tint B i t) 0‖ ≤ C) :
    ‖iteratedFDeriv ℝ r (Tones.tint B i t) 0 v‖ ≤ (Fintype.card (Fin r → Fin (d+1)):ℝ)*C*M^r*u^(T.grades i).1 := by
  classical
  let E:= Dev B.stencil G
  let f:=Tones.tint B i t; let n:= (T.grades i).1
  choose w hw hW hv using fun i=>(hV i).2
  let H := iteratedFDeriv ℝ r f 0
  have hu':=hu.1
  have hx (a : Fin r → Fin (d+1)) : ‖H (fun i=> w i (a i))‖ ≤ C*M^r*u^n := by
    let g j := (a j).val+1
    by_cases hH : ∑ j,g j < n
    · have he' (j : Fin r) : ∃ f : Potential G, f ∈ rangeLt (Axis→G.Color) (g j) ∧ w j (a j)=ping B.stencil f := by
        have hh' := (Finset.single_le_sum (f:=g) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)).trans_lt (hH.trans_le (T.bound i))
        let v : Fin d := ⟨(a j).val, Nat.lt_of_succ_lt hh'⟩
        exact hv j v
      choose Y hY hV' using he'; simp_rw [hV']
      rw [show H (fun j => _) = _ from Tones.columnCostLower A B h i t g hH Y hY,norm_zero]; positivity
    apply (H.le_opNorm _).trans
    apply (mul_le_mul hh (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> hW j (a j))) (by positivity) hC).trans
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.prod_pow_eq_pow_sum,← mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hu' hu.2 (le_of_not_gt hH)) (by positivity)
  change ‖H v‖ ≤ _; rw [funext hw,H.map_sum w]; apply (norm_sum_le ..).trans
  apply (Finset.sum_le_sum fun a _=> hx a).trans_eq; simp [mul_assoc,n]

/-- Derivatives away from 0 on the true stencil. Test every parameter tensor
under Constraints; not opNorm bounds for arbitrary O(L⁻¹) directions. -/
def OnSway (r : ℕ) (M C : ℝ) : Prop :=
    0≤C ∧ ∀ t∈ Ioc (0:ℝ) 1, ∀ u∈Icc (0:ℝ) 1, ∀ v : Fin r→Dev B.stencil G,
      (∀ i, Rolls B.stencil d (v i) u M) → ∀ w, Rolls B.stencil d w u M → ∀ s∈Icc (0:ℝ) 1,
      ‖iteratedFDeriv ℝ r (Tones.tint B i t) (s • w) v‖ ≤ C*u^((T.grades i).1)

-- call columnPrice with larger margin than all stencils thresholds actually need.
def screen (d : ℕ) (M : ℝ) := (d+1:ℕ)*M

lemma screened {w : Dev S G} {s : ℝ} (hu : u∈Icc 0 1) (hw : Rolls S d w u M) (hs : s∈Icc 0 1) :
    ‖s • w‖≤screen d M := by
  have hm := hw.1
  rw [norm_smul,Real.norm_of_nonneg hs.1]
  refine (mul_le_mul hs.2 (hw.normed hu) (norm_nonneg _) zero_le_one).trans ?_
  rw [one_mul]; exact mul_le_of_le_one_right (by positivity) hu.2

include b in
private lemma long_path (r : ℕ) (hR : d ≤ r) (M : ℝ) (hM : 0≤M) : ∃ C:ℝ, OnSway B i r M C := by
  let A:=screen d M; have hA : 0≤A := by unfold A screen; positivity
  obtain ⟨C,hC,H⟩:= Tones.columnPrice B b i r A
  let l:=(T.grades i).2
  let Z:=C*(1+A)^l
  have hZ:0≤Z:=by unfold Z; positivity
  refine ⟨Z*A^r,mul_nonneg hZ (by positivity),fun t ht u hu v hv w hw s hs => ?_⟩
  let f:=Tones.tint B i t
  have he := screened hu hw hs
  have hy : t∈Icc 0 1 := ⟨ht.1.le,ht.2⟩
  have hc : ‖iteratedFDeriv ℝ r f (s • w)‖ ≤ Z := by
    apply (H r le_rfl t (s • w) ht _).trans
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add_right he _) _) hC
    rw [norm_smul,Real.norm_of_nonneg hy.1]; exact (mul_le_of_le_one_left (norm_nonneg _) hy.2).trans he
  have hh j : ‖v j‖≤A*u := (hv j).normed hu
  apply ((iteratedFDeriv ℝ r f _).le_opNorm _).trans
  apply (mul_le_mul hc (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> hh j)) (by positivity) hZ).trans
  simpa only [Finset.prod_const, Finset.card_univ,Fintype.card_fin,mul_pow,← mul_assoc] using!
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hu.1 hu.2 ((T.bound i).trans hR)) (show 0≤Z*A^r by positivity)

include b h
private lemma extend_sway (r : ℕ) (M C : ℝ) (hM : 0≤M) (hH : OnSway B i (r+1) M C) : ∃ D:ℝ, OnSway B i r M D := by
  classical
  obtain ⟨K,hp,hf⟩:=Tones.columnPrice B b i r 0
  let D:=(Fintype.card (Fin r→Fin (d+1)):ℝ)*K*M^r
  have hD : 0≤D:= by unfold D; positivity
  refine ⟨C+D, add_nonneg hH.1 hD,fun t ht u hu v hv w hw s hs =>?_⟩
  let f:= Tones.tint B i t; let g (s:ℝ) := iteratedFDeriv ℝ r f (s • w) v
  let n:= (T.grades i).1
  have he : ‖g 0‖ ≤ D*u^n := by unfold g; rw [zero_smul]; apply at_launch A B h i r v hu hM hv K hp; simpa using hf r le_rfl t 0 ht (by simp)
  have hd (s : ℝ) : HasDerivAt g (iteratedFDeriv ℝ (r+1) f (s • w) (Fin.cons w v)) s := by
    have hh : ContDiff ℝ ω f := Tones.coat_smooth (column_smooth B i) _ _
    have hb : ContDiffAt ℝ (↑(r+1:ℕ)) f (s • w) := hh.contDiffAt.of_le le_top
    rw [YM.Analysis.cons_jet hb]
    have hy := ((ContinuousMultilinearMap.apply ℝ _ ℂ v).differentiableAt.comp (s • w)
      (hb.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr r.lt_succ_self))).hasFDerivAt
    exact hy.comp_hasDerivAt s (by simpa only [one_smul] using (hasDerivAt_id' (s:ℝ)).smul_const w)
  have hC:=hH.1; have hu':=hu.1
  let l:=C*u^n; have hl : 0≤l:=by unfold l; positivity
  have hv' (i : Fin (r+1)) : Rolls B.stencil d (Fin.cons (α:=fun _ => Dev B.stencil G) w v i) u M := by
    refine Fin.cases ?_ (fun j=> ?_) i
    · simpa using hw
    simpa using hv _
  have H := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (fun s _=> (hd s).hasDerivWithinAt)
    (fun s hs => show ‖_‖ ≤ l from hH.2 t ht u hu (Fin.cons w v) hv' w hw s hs) (x:=0) (by simp) hs
  rw [sub_zero, Real.norm_of_nonneg hs.1] at H
  change ‖g s‖ ≤ _
  rw [add_mul]
  refine (norm_le_norm_sub_add _ _).trans (add_le_add (H.trans (mul_le_of_le_one_right hl hs.2)) he)

-- L independent top/bottom crossover. Threshold f PAID positive <=1.
theorem earns (r : ℕ) (M : ℝ) (hM : 0≤M) : ∃ C : ℝ, OnSway B i r M C := by
  by_cases hr : r ≤ d
  · induction hr using Nat.decreasingInduction with
    | self => exact long_path B b i d le_rfl M hM
    | of_succ r hr ih => obtain ⟨C,hC⟩:=ih; exact extend_sway A B h b i r M C hM hC
  exact long_path B b i r (by omega) M hM
end
end YM.Planned.PrimaryIntegral295.Units
