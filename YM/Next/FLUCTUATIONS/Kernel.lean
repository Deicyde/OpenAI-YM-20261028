import YM.Next.FLUCTUATIONS.Charts

/-!
# Compare kernel factors of the defects to full flat matrices

Cover before cut, pay each residue type. Uniform row *and* transpose row
absolute estimates even for short tori. Transported on the true winding
paths, and compose only after cuts. All numerical cut distances in fine
units. Gain is post-L; this isn't a new pre-L `Allowance`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Laurent
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {c f n : Side} {S : StepData c f}

section cost
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Unlocalized row/column price. -/
structure Both (F : X → Y → Pay G) (C : ℝ) : Prop where
  rows (i : X) : ∑ j, ‖F i j‖ ≤ C
  cols (j : Y) : ∑ i, ‖F i j‖ ≤ C

lemma Both.mono {F : X → Y → Pay G} {C D : ℝ} (h : Both F C) (he : C ≤ D) : Both F D :=
  ⟨fun i => (h.rows i).trans he, fun i => (h.cols i).trans he⟩

structure NearFlat (F E : X → Y → Pay G) (C u : ℝ) : Prop where
  cut : Both F C
  full : Both E C
  close : Both (F-E) (C*u)

lemma NearFlat.mono {F E : X → Y → Pay G} {C u D v : ℝ} (h : NearFlat F E C u) (hd : 0 ≤ D)
    (hu : 0 ≤ u) (hl : C ≤ D) (hv : u ≤ v) : NearFlat F E D v :=
  ⟨h.cut.mono hl,h.full.mono hl,h.close.mono (mul_le_mul hl hv hu hd)⟩

end cost

private lemma scalar_bound (G : Gauge) (x : ℝ) : ‖scalar G x‖ ≤ ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun i => (norm_smul x i).le

private lemma scalar_zero : scalar G 0 = 0 := by ext x; simp [scalar]

lemma rated_norm_sub (U : Config G n) (x : Site n) (w : Walk) (a : ℝ) :
    ‖rated U x w a - scalar G a‖ ≤ (2 * G.colorScale * G.chord (travel U x w)) * ‖a‖ := by
  let t := travel U x w
  have hh := G.colorScale_pos
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg (by positivity)
    (G.chord_nonneg t)) (norm_nonneg _)) (fun i => ?_)
  change ‖a • (G.adjoint t i) - a • i‖ ≤ _
  rw [← smul_sub,norm_smul]
  exact (mul_le_mul_of_nonneg_left (adjoint_norm_sub t i) (norm_nonneg _)).trans_eq (by ring)

section machine
variable {α β X Y : Type*} [Fintype α] [Fintype β] [Fintype X] [Fintype Y]
    (p : X ≃ Co c α) (q : Y ≃ Co c β) (K : Row α β)

/-- Counting lemma via E03 physical absolute envelope; use only its sum
part (full terms may have no useful stencil). -/
private lemma covered_prices (F : X → Y → Cover → Pay G) (η A : ℝ)
    (hK : K.strip η A) (hA : 0 ≤ A) (δ : ℝ) (hd : 0 ≤ δ)
    (he : ∀ i j u, ‖F i j u‖ ≤ if (q j).1 = (p i).1 + wrap c u then
      δ * (Real.exp (η*size u) * ‖K (p i).2 (q j).2 u‖) else 0) :
    (∀ i j, Summable (F i j)) ∧ Both (fun i j => ∑' u, F i j u)
      (((Fintype.card α:ℝ)+(Fintype.card β:ℝ))*A*δ) := by
  let M : Row α β := fun i j u => δ * (Real.exp (η*size u)*‖K i j u‖)
  have hv i j u : 0 ≤ M i j u := by unfold M; positivity
  have hm : M.strip 0 (δ*A) := by
    intro i j
    have hh := hK i j
    simp only [Width,hv, Real.norm_of_nonneg, zero_mul,Real.exp_zero,one_mul]
    refine ⟨hv _ _, hh.2.1.mul_left δ,?_⟩
    unfold M; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hh.2.2 hd
  have ht : ∀ i j u, ‖F i j u‖ ≤ if (q j).1=(p i).1+wrap c u then ‖M (p i).2 (q j).2 u‖ else 0 := by
    simp only [Real.norm_of_nonneg (hv ..)]; exact he
  refine ⟨fun i j => ?_,?_⟩
  · refine Summable.of_norm_bounded ((hm (p i).2 (q j).2).unweighted le_rfl).2.1 (fun u => (ht i j u).trans ?_)
    split <;> simp
  let reach (i : X × Y) := separation (p i.1).1 (q i.2).1
  have hf := Work.E03.anchored_of_terms M p q F (50*univ.sup reach) (by rfl : (0:ℝ)≤0) hm ht (by
    intro i j u _
    have h : separation (p i).1 (q j).1 ≤ univ.sup reach := le_sup (s:=univ) (f:=reach) (mem_univ (i,j))
    omega)
  have h1 : 0 ≤ (Fintype.card α:ℝ)*A*δ := by positivity
  have h2 : 0 ≤ (Fintype.card β:ℝ)*A*δ := by positivity
  refine ⟨fun i => (hf.rows i).trans ?_,fun j => (hf.columns j).trans ?_⟩ <;> linarith

variable (d R : ℕ) (x : X → Site n) (w : X → Cover → Walk) (W : Config G n)

def routedTerm (i : X) (j : Y) (u : Cover) : Pay G :=
  if (w i u).length*d ≤ R ∧ (q j).1=(p i).1+wrap c u then
    rated W (x i) (w i u) (K (p i).2 (q j).2 u) else 0

-- post-L price; d or path itself includes *physical* cutoff metric scale.
def bothPrice (G : Gauge) (α β : Type*) [Fintype α] [Fintype β] (A η C : ℝ) :=
  ((Fintype.card α : ℝ) + (Fintype.card β : ℝ)) * A * (1+2*G.colorScale*C+Real.exp η)

private lemma routed_price (D η A C h : ℝ) (hp : 0<D) (he : 0<η) (hA : 0≤A) (hC : 0≤C)
    (hh : 0≤h) (hd : 1≤d) (hw : ∀ i u, (((w i u).length*d:ℕ):ℝ) ≤ D*(1+size u))
    (hv : ∀ i, G.chord (W i) ≤ C*h) (hK : K.strip η A) :
    NearFlat (fun i j => ∑' u, routedTerm p q K d R x w W i j u)
      (fun i j => scalar G (K.acts c (p i) (q j))) (bothPrice G α β A η C) (widen R h (η/D)) := by
  let f := routedTerm p q K d R x w W
  let cTerm (i j) (u : Cover) := if (q j).1=(p i).1+wrap c u then K (p i).2 (q j).2 u else 0
  let g (i j) u := scalar G (cTerm i j u)
  have hm i j : ∑' u, g i j u = scalar G (K.acts c (p i) (q j)) := by
    have hc : Summable (cTerm i j) := by
      apply Summable.of_norm_bounded ((hK (p i).2 (q j).2).unweighted he.le).2.1; intro u
      dsimp only [cTerm]; split <;> simp
    exact (hc.hasSum.smul_const (ContinuousLinearMap.id ℝ G.Color)).tsum_eq
  have hExp (u : Cover) : 1 ≤ Real.exp (η*size u) := Real.one_le_exp (by positivity)
  have hEntry i j u : ‖K i j u‖ ≤ 1*(Real.exp (η*size u)*‖K i j u‖) := by
    rw [one_mul]; exact le_mul_of_one_le_left (norm_nonneg _) (hExp u)
  obtain ⟨hs,hf⟩ := covered_prices p q K f η A hK hA 1 zero_le_one (by
    intro i j u
    dsimp only [f,routedTerm]
    split
    next h => rw [if_pos h.2]; exact (Work.E03.norm_rated_le ..).trans (hEntry ..)
    next h => (split <;> simp); positivity)
  obtain ⟨ht,hg⟩ := covered_prices p q K g η A hK hA 1 zero_le_one (by
    intro i j u
    dsimp only [g,cTerm]
    split
    next h => exact (scalar_bound ..).trans (hEntry ..)
    next h => rw [scalar_zero]; simp)
  let J := 1+2*G.colorScale*C+Real.exp η
  have hJ : 1 ≤ J := by
    have h1 : 0 ≤ 2*G.colorScale*C := by have := G.colorScale_pos; positivity
    unfold J; linarith [Real.exp_pos η]
  let b := widen R h (η/D)
  have hb : 0 ≤ b := widen_nonneg _ hh
  have hB : ((Fintype.card α:ℝ)+(Fintype.card β:ℝ))*A*1 ≤ bothPrice G α β A η C :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  simp_rw [← hm]
  refine ⟨hf.mono hB, hg.mono hB, ?_⟩
  let F (i : X) (j : Y) u := f i j u-g i j u
  have hl := (covered_prices p q K F η A hK hA (J*b) (mul_nonneg (by linarith) hb) ?_).2
  · change Both ((fun i j => ∑' u, f i j u) - (fun i j => ∑' u, g i j u)) _
    have hx : (fun i j => ∑' u, f i j u) - (fun i j => ∑' u, g i j u) =
        (fun i j => ∑' u, F i j u) := by
      funext i j; exact ((hs i j).tsum_sub (ht i j)).symm
    rw [hx]
    apply hl.mono (le_of_eq (by unfold J b bothPrice; ring))
  intro i j u
  let E := Real.exp (η*size u)
  let y := w i u
  let a := K (p i).2 (q j).2 u
  dsimp only [F,f,routedTerm,g,cTerm]
  by_cases hn : (q j).1=(p i).1+wrap c u
  swap
  · simp only [hn, and_false,↓reduceIte, scalar_zero,sub_zero,norm_zero,le_refl]
  simp only [hn,and_true,↓reduceIte]
  split
  next ht =>
    have hd' : (y.length:ℝ) ≤ R := by
      have h := le_trans (show y.length ≤ y.length*d from le_mul_of_one_le_right (Nat.zero_le _) hd) ht
      exact_mod_cast h
    have hu : 2*G.colorScale * G.chord (travel W (x i) y) ≤ J*b := calc
      _ ≤ 2*G.colorScale*(y.length*(C*h)) := by
        have hh₁ := G.colorScale_pos; gcongr; exact travel_chord W y (x i) (C*h) hv
      _ = (2*G.colorScale*C) * ((y.length:ℝ)*h) := by ring
      _ ≤ J*b := by
        apply mul_le_mul
        · unfold J; linarith [Real.exp_pos η]
        · exact (mul_le_mul_of_nonneg_right (le_trans hd' (by simp)) hh).trans
            (le_add_of_nonneg_right (by positivity))
        · positivity
        · linarith
    exact (rated_norm_sub W (x i) y a).trans
      (mul_le_mul hu (by simpa only [one_mul] using hEntry (p i).2 (q j).2 u)
        (norm_nonneg _) (mul_nonneg (by linarith) hb))
  next ht =>
    have hz : (R:ℝ) ≤ D * (1+size u) :=
      (show (R:ℝ) ≤ ((y.length*d : ℕ):ℝ) by exact_mod_cast le_of_lt (Nat.lt_of_not_ge ht)).trans (hw i u)
    have hx : η/D*R ≤ η + η*size u := calc
      _ ≤ η/D*(D*(1+size u)) := by gcongr
      _ = _ := by field_simp
    have hu : 1 ≤ J*b*E := calc
      _ ≤ Real.exp η*Real.exp (-(η/D)*R)*E := by
        rw [← Real.exp_add, show E = _ from rfl, ← Real.exp_add]
        apply Real.one_le_exp; linarith
      _ ≤ _ := by
        have h2 : Real.exp η ≤ J := le_add_of_nonneg_left (by have := G.colorScale_pos; positivity)
        have h3 : Real.exp (-(η/D)*R) ≤ b := by
          unfold b widen; exact le_add_of_nonneg_left (by positivity)
        gcongr
    rw [zero_sub,norm_neg]
    exact (scalar_bound G a).trans
      ((le_mul_of_one_le_left (norm_nonneg a) hu).trans_eq (mul_assoc _ E ‖a‖))
end machine
section bounds
-- `route` at order 1, while wraps may be arbitrary
private lemma route_size (x y : Cover) : (route x y 1).length = size (y-x) := by
  have ha : allAxes 1 = [0,1,2,3] := by decide
  simp [route, axisRoute,ha,size,Fin.sum_univ_succ,straight,Axis]

private lemma size_scaled (x : Cover) (d : ℕ) : size (d • x) = d * size x := by
  simp [size,Pi.smul_apply,Int.natAbs_mul, Finset.mul_sum]

private lemma max_lift (L : Side) (x : Site L) : size (lift x) ≤ 4 * L.val := calc
  _ ≤ ∑ _i : Axis, L.val := Finset.sum_le_sum fun i _ => by have hh := lift_centers x i; omega
  _ = _ := by simp [Axis]

private def elasticity (L : Side) : ℝ := 5*(L.val:ℝ)
private lemma elasticity_pos (L : Side) : 0 < elasticity L := by
  unfold elasticity; have := L.property; positivity

section lanes
variable {α β X Y : Type*} [Fintype α] [Fintype β] [Fintype X] [Fintype Y]
    (p : X ≃ Co c α) (q : Y ≃ Co c β) (K : Row α β)

private lemma lane_prices (L : Side) (R : ℕ) (V : Config G c) {η A C h : ℝ} (he : 0<η) (hA : 0≤A) (hC : 0≤C)
    (hh : 0≤h) (hv : ∀ i, G.chord (V i) ≤ C*h) (hK : K.strip η A) :
    NearFlat (fun i j => lane R L.val V K (p i) (q j))
      (fun i j => scalar G (K.acts c (p i) (q j))) (bothPrice G α β A η C)
        (widen R h (η/elasticity L)) := by
  refine routed_price p q K L.val R (fun i => (p i).1) (fun _ u => route 0 u 1) V (elasticity L) η A C h
    (elasticity_pos _) he hA hC hh L.property ?_ hv hK
  intro i u
  simp only [route_size,sub_zero,Nat.cast_mul,elasticity]
  have ht : 0 ≤ (L.val:ℝ)*(size u:ℝ) := by positivity
  linarith
end lanes

private lemma mf_prices (T : Tube G S) (R : ℕ) (V : Config G c) {η A C h : ℝ} (he : 0<η) (hA : 0≤A) (hC : 0≤C)
    (hh : 0≤h) (hv : ∀ i, G.chord (V i) ≤ C*h) (hK : T.R.mf.strip η A) :
    NearFlat (T.Φ R V) (flatF T)
      (bothPrice G (Co S.patch.L Layers2) Layers2 A η C) (widen R h (η/elasticity S.patch.L)) := by
  let K := T.R.mf
  let x := fun i : Twin f => (mesh i).1
  let p := (Work.E03.meshEquiv f).trans (splitCo S.ratio Layers2)
  let q := Work.E03.meshEquiv c
  let L := S.patch.L
  let V' := replica S.ratio V
  let w := fun i u => route (lift (S.ratio.residue (x i))) (S.patch.L.val • u) 1
  have hb (i j u) : routedTerm p q K 1 R x w V' i j u =
      casted S T.R R V (mesh i) (mesh j) u := by
    unfold routedTerm casted p
    rw [Equiv.trans_apply, split_co, mul_one]; rfl
  have hp i : G.chord (V' i) ≤ C*h := by
    dsimp only [V',replica]
    split
    next h => rw [G.chord_one]; positivity
    next h => exact hv _
  have ht := routed_price p q K 1 R x w V' (elasticity L) η A C h
    (elasticity_pos _) he hA hC hh le_rfl (by
      intro i u
      let z := S.ratio.residue (x i)
      have hSize : size (L.val • u - lift z) ≤ L.val * size u + 4 * L.val := by
        rw [sub_eq_add_neg]; apply (size_add ..).trans
        rw [size_neg, size_scaled]; exact Nat.add_le_add_left (max_lift L z) _
      have hl : (size (L.val • u - lift z):ℝ) ≤ L.val * (size u:ℝ) + 4 * (L.val:ℝ) := by
        exact_mod_cast hSize
      simp only [w,mul_one,route_size]; apply hl.trans; unfold elasticity
      have hx : 0 ≤ (L.val:ℝ)*(size u:ℝ) := by positivity
      linarith) hp hK
  simp_rw [hb] at ht
  exact ht

/-- Combine the prices only after L. Period-, store- and cut-independent
    prices. Inputs all quantified at a fixed patch L (including degenerate
    periods at this interface). -/
lemma kernel_chart_cost (G : Gauge) (L : Side) (η E : ℝ) (he : 0<η) :
    ∃ C τ r : ℝ, 0<C ∧ 0<τ ∧ 0<r ∧
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch.L=L →
        (∃ N : ℕ, T.R.Deep η E N) → ∀ (R : ℕ) (b : LogField G c) (h : ℝ), ‖b‖ ≤ h → h ≤ r →
          NearFlat (T.Φ R (represent b)) (flatF T) C (widen R h τ) ∧
          NearFlat (T.Φ' R (represent b)) (flatI T) C (widen R h τ) ∧
          NearFlat (T.N R (represent b)) (flatN T) C (widen R h τ) := by
  obtain ⟨Y,r,hY,hr,hb⟩ := chord_chart_cost G
  let A := max (max 0 E) (E/(L.val:ℝ)^2)
  let C₁ := bothPrice G (Co L Layers2) Layers2 A η Y
  let C₂ := bothPrice G (TypeFace 1) Layers2 A η Y
  let C₃ := bothPrice G Gain Layers2 A η Y
  let C := max 1 (max C₁ (max C₂ C₃))
  have hC : 0<C := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨C,η / elasticity L,r,hC, div_pos he (elasticity_pos _),hr,?_⟩
  intro c f S T hl hK R b h hv ht
  subst L
  have hx (i : Bond c) : G.chord (represent b i) ≤ Y*h := by
    have he := (norm_le_pi_norm b (pole i)).trans hv
    change G.chord (G.lieExp (b (pole i))*1) ≤ _
    rw [mul_one]; exact (hb _ (he.trans ht)).trans (mul_le_mul_of_nonneg_left he hY.le)
  have hA : 0≤A := (le_max_left ..).trans (le_max_left ..)
  have hu : E≤A := (le_max_right ..).trans (le_max_left ..)
  obtain ⟨N,h1,h2,h3,-⟩ := hK
  have hh := le_trans (norm_nonneg _) hv
  have hz := widen_nonneg (τ:=η/elasticity S.patch.L) R hh
  have hm : NearFlat (T.Φ R (represent b)) _ C₁ (widen R h (η / elasticity S.patch.L)) :=
    mf_prices T R _ he hA hY.le hh hx fun i j => (h3 i j).mono le_rfl (le_max_right ..)
  have hn := lane_prices (Work.E03.poleEquiv c) (Work.E03.meshEquiv c) _ S.patch.L R _ he hA hY.le hh hx
    (fun i j => (h1 i j).mono le_rfl hu)
  have ho := lane_prices (Equiv.refl _) (Work.E03.meshEquiv c) _ S.patch.L R _ he hA hY.le hh hx
    (fun i j => (h2 i j).mono le_rfl hu)
  exact ⟨hm.mono hC.le hz (le_max_of_le_right (le_max_left _ _)) le_rfl,
    hn.mono hC.le hz (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))) le_rfl,
    ho.mono hC.le hz (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))) le_rfl⟩
end bounds
end YM.Next.Fluctuations
