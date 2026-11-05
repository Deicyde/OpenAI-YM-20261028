import YM.Next.UV_STRESS.Plateau


/-!
# Obtain all-window, all-exterior physical fields
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Filter Function Set MeasureTheory Analysis Extraction Table Ward Climb Work.A01
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {n d D : ℕ}

lemma slide_disc (H : S.Hierarchy) (x : Points n) (s : E4) (hx : x∈conf _) (q : Fin n → S.Tag) :
    disc q (Points.across s x)=disc q x :=
  let v : Fin n → L.Token := fun i => ⟨(q i).1,S.representative _ (q i).2⟩
  H.translations n x hx s v

lemma valid_nearby {x : Points (n+1)} {w : E4 → ℝ} (hx : x∈conf _) (ht : Window x w) :
    ∀ᶠ y in 𝓝 x,y∈conf _ ∧ Window y w := by
  have he (i : Fin (n+1)) : Tendsto (fun v : Points (n+1) => v i) (𝓝 x) (𝓝 (x i)) :=
    (show Continuous (fun v : Points (n+1) => v i) from by fun_prop).continuousAt
  have hy := (he 0).eventually (eventually_eventuallyEq_nhds.mpr ht.2.2.1)
  have hh (i : Fin n) := (he i.succ).eventually ((isClosed_tsupport w).isOpen_compl.mem_nhds
    (show x i.succ∈ (tsupport w)ᶜ from ht.2.2.2 _))
  filter_upwards [(conf_open _).mem_nhds hx,hy,eventually_all.mpr hh] with z hp hi hh
  exact ⟨hp,ht.1,ht.2.1,hi,hh⟩

lemma moves_window {x : Points (n+1)} {w : E4→ℝ} (s : E4) (h : Window (Points.across s x) w) :
    Window x (fun y => w (y+s)) := by
  have hp (i : Fin (n+1)) : Tendsto (fun y : E4 => y+s) (𝓝 (x i)) (𝓝 (x i+s)) :=
    (show Continuous (fun y : E4 => y+s) from by fun_prop).continuousAt
  refine ⟨h.1.comp (contDiff_id.add contDiff_const),h.2.1.comp_homeomorph (Homeomorph.addRight s),
    h.2.2.1.comp_tendsto (hp 0),fun i => ?_⟩
  exact notMem_tsupport_iff_eventuallyEq.mpr ((notMem_tsupport_iff_eventuallyEq.mp (h.2.2.2 i)).comp_tendsto (hp i.succ))

/-- Measure is ambient d⁴y. -/
lemma moves_flux (H : S.Hierarchy) {x : Points (n+1)} (hx : x∈conf _) (s : E4) {w : E4→ℝ}
    (U : E4 → E4) (J : S.Stress) (q : Fin n → S.Tag) (v : S.Field d) (h : Window (Points.across s x) w) :
    flux J w (fun y => U (y- (Points.across s x) 0)) (Points.across s x) q v =
      flux J (fun y => w (y+s)) (fun y => U (y - x 0)) x q v := by
  have hy (y : E4) (a : Axis) : Analysis.D (basis a) (fun y : E4 => w (y+s)) y=Analysis.D (basis a) w (y+s) := by
    change fderiv ℝ (w ∘ fun y : E4 => y+s) y _=_
    have he : HasFDerivAt (fun y : E4 => y+s) (ContinuousLinearMap.id ℝ _) y := (hasFDerivAt_id _).add_const _
    rw [fderiv_comp y (h.1.differentiable (by simp) _) he.differentiableAt,he.fderiv]; rfl
  have hh (y : E4) : Points.cons (y+s) (Points.across s x)=Points.across s (Points.cons y x) := by
    ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons]
  have hw (i j : Axis) (y : E4) : term J w (fun y => U (y-(Points.across s x) 0))
      (Points.across s x) q v i j (y+s)=term J (fun y => w (y+s)) (fun y => U (y-x 0)) x q v i j y := by
    unfold term; dsimp only; rw [hx_center, ← hy, hh]
    by_cases hz : Analysis.D (basis i) (fun y => w (y+s)) y=0
    · simp [hz]
    exact congr_arg (fun a : ℂ => _ * a) (slide_disc H (Points.cons y x) s (separated_of_D hx (moves_window _ h) hz) _)
  unfold flux
  apply congr_arg Neg.neg; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  rw [← integral_add_right_eq_self _ s]; simp_rw [hw]
where
  hx_center (y : E4) : y+s-(Points.across s x) 0=y-x 0 := by simp

lemma continuous_flux (H : S.Hierarchy) {x : Points (n+1)} (hx : x∈conf _) {χ : E4 → ℝ} (hw : Window x χ)
    (U : E4 → E4) (hU : ∀ i : Axis, Continuous (fun y => U y i)) (J : S.Stress) (q : Fin n → S.Tag) (v : S.Field d) :
    ContinuousAt (fun y : Points (n+1) => flux J χ (fun z => U (z-y 0)) y q v) x := by
  classical
  let X := {y : Points (n+1)|y ∈ conf _ ∧ Window y χ}
  let K := tsupport (fderiv ℝ χ)
  have hK : IsCompact K := hw.2.1.fderiv ℝ
  have ht : x∈X:=⟨hx,hw⟩
  let F (i j : Axis) (y : Points (n+1)) z := term J χ (fun z => U (z-y 0)) y q v i j z
  have he (i j : Axis) (p z) (hz : z∉K) : F i j p z=0 := by simp [F,term,Analysis.D,image_eq_zero_of_notMem_tsupport hz]
  have hF (i j : Axis) : ContinuousOn (uncurry (F i j)) (X ×ˢ univ) := by
    rintro ⟨y,z⟩ ⟨⟨hp,H'⟩,_⟩; apply ContinuousAt.continuousWithinAt
    by_cases hb : z∈K
    · have he : Continuous (fun z => Analysis.D (basis i) χ z) :=
        (hw.1.continuous_fderiv (by simp)).clm_apply continuous_const
      have hD : Continuous (fun p : Points (n+1) × E4 => ((((Analysis.D (basis i) χ p.2) * U (p.2-p.1 0) j:ℝ):ℂ))) :=
        Complex.continuous_ofReal.comp ((he.comp continuous_snd).mul ((hU j).comp (show Continuous (fun p : Points (n+1) × E4 => p.2-p.1 0) by fun_prop)))
      exact hD.continuousAt.mul ((cont_disc H (Fin.cons ⟨4,J i j⟩ (Fin.cons ⟨d,v⟩ q)) (window_separated hp H' hb)).continuousAt.comp
        (f:=fun a : Points (n+1) × E4 => Points.cons a.2 a.1) (x:=(y,z)) (Work.A02.continuous_cons.comp continuous_swap).continuousAt)
    have hZ := (continuous_snd (X:=Points (n+1))).continuousAt (x:=(y,z))|>.tendsto.eventually
      ((isClosed_tsupport (fderiv ℝ χ)).isOpen_compl.mem_nhds hb)
    exact continuousAt_const.congr (hZ.mono fun p hv => (he i j p.1 p.2 hv).symm)
  have hg (i j : Axis) : ContinuousAt (fun p => ∫ z,F i j p z) x :=
    ((continuousOn_integral_of_compact_support hK (hF i j) (fun p z _ => he i j p z)) x ht).continuousAt
      (show X∈𝓝 x from valid_nearby hx hw)
  exact (tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ (fun j _ => hg i j))).neg

section ground
variable {C : Family G} {S : Table C.book} {F : Extraction.Order} {V : DiffPlan S}

lemma meets_grid (C : Family G) (x : Points n) :
    ∃ᶠ y in 𝓝 x, y∈generic n ∧ ∃ k : ℕ, ∃ v, y=Extraction.Order.grid C k v := by
  apply mem_closure_iff_frequently.mp
  have he (y) (hy : y∈generic n) : y∈closure {y | y∈generic n ∧ ∃ k : ℕ, ∃ v, y=Extraction.Order.grid C k v} := by
    let u k := address (C.S.a k) y
    let g k := Extraction.Order.grid C k (u k)
    have ht : Tendsto g atTop (𝓝 y) := chosen y
    apply isClosed_closure.mem_of_tendsto ht
    filter_upwards [ht.eventually ((genericOpen n).mem_nhds hy)] with k hk using
      subset_closure (show g k ∈ {y|y∈generic n∧∃ k : ℕ, ∃ v, y = Extraction.Order.grid C k v} from ⟨hk,k,u k,rfl⟩)
  exact (closure_minimal he isClosed_closure) (Dash.full n x)

private lemma raised (k : ℕ) {v : Fin (n+1)→Lattice.Cover} (h : Extraction.Order.grid C k v∈generic _)
    (q : Fin n → S.Tag) : ∃ (x : Points (n+1)) (s : E4) (p : Fin n → C.book.Token) (z : Fin n → Lattice.Cover),
      x = Extraction.Order.grid C k (Fin.cons 0 z) ∧ x∈generic _ ∧ Points.across s x=Extraction.Order.grid C k v ∧
      (S.classTokens ∘ p=q) := by
  let s := C.S.gridPoint k (v 0)
  let z i := v (Fin.succ i)-v 0
  let x := Extraction.Order.grid C k (Fin.cons (α:=fun _ => Lattice.Cover) 0 z)
  have hx : x=Points.across (-s) (Extraction.Order.grid C k v) := by
    ext1 i
    refine Fin.cases ?_ (fun j => ?_) i
    · ext a; simp [s,x,Extraction.Order.grid,Schedule.gridPoint]
    ext a; simp [s,z,x,Extraction.Order.grid,Schedule.gridPoint,mul_sub]; ring
  refine ⟨x,s,(expose ∘ q),z,rfl,hx.symm ▸ Extraction.Order.nearGeneric (-s) h,?_,?_⟩
  · rw [hx]; ext i; simp
  exact funext fun i => Ward.sends_back _

lemma observes (H : S.Hierarchy) (D : ℕ) : Injective (LinearMap.pi (fun I : Watch C => I.tester S D)) := by
  intro a b he
  apply S.field_ext H.laws.toSymmetric
  intro n q x hx
  let K (v : S.Field D) := disc (Fin.cons ⟨D,v⟩ q)
  have hs v : ContinuousAt (K v) x := (cont_disc H _ hx).continuousAt
  refine tendsto_nhds_unique_of_frequently_eq (hs a) (hs b) ?_
  refine (meets_grid C x).mono ?_
  rintro u ⟨hp,k,t,rfl⟩
  obtain ⟨_,s,p,z,rfl,hx,ht,hq⟩ := raised (C:=C) k hp q
  let I : Watch C := ⟨n,k,z,p,hx⟩
  have hK v : K v (Extraction.Order.grid C k t)=I.tester S D v := by
    rw [← ht]; change disc _ (Points.across s I.held)=_
    rw [slide_disc H I.held _ I.distinct, Watch.test_known]; change _ = disc (Fin.cons ⟨D,v⟩ (S.classTokens ∘ p)) _; rw [hq]
  exact (hK a).trans ((congr_fun he I).trans (hK b).symm)

-- finite values in the image of the same evaluation. No nonzero label
-- cap assumption. No integral dummy representative off chosen Window.
private theorem obtainable {ι Y : Type*} [Fintype ι] [AddCommGroup Y] [Module ℂ Y]
    (R : Y →ₗ[ℂ] (ι → ℂ)) (p : ι → ℂ)
    (h : ∀ g : ι→ℂ,(∀ v : Y, (∑ i, g i*R v i)=0) → (∑ i, g i*p i)=0) :
    ∃ v, R v=p := by
  classical
  suffices he : p∈LinearMap.range R from he
  by_contra H
  let S := LinearMap.range R
  have he : S.mkQ p≠0 := fun hv => H ((Submodule.Quotient.mk_eq_zero _).mp hv)
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero ℂ he
  let L := f.comp S.mkQ
  let g (i : ι) := L (Pi.single i 1)
  have hh (w : ι → ℂ) : L w= ∑ i, g i * w i := by
    have he : w= ∑ i : ι, w i • Pi.single i 1 := by
      funext j; simp [Pi.single_apply,apply_ite]
    conv_lhs => rw [he]
    rw [map_sum]; apply Finset.sum_congr rfl; intro i _; simp [mul_comm,g]
  apply hf
  change L p=0
  rw [hh]; apply h g
  intro v; rw [← hh]; unfold L; rw [LinearMap.comp_apply, show S.mkQ _=0 from
    (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self ..),map_zero]

-- Flux coverage at all x.
theorem annular_field (hC : C.Makes) (hq : Cells.CellHyp C F) (ho : F.PointLimits C S)
    (H : S.Hierarchy) (h : V.Derivatives S) {J : S.Stress} (hc : Conserved V H.spin J) (v : S.Field d)
    (U : E4→E4) (hw : ∀ i : Axis,ContDiff ℝ ∞ (fun y => U y i)) (hl : killing U) (p : ℕ)
    (hg : ∀ y (r : ℝ),0<r → U (r • y)=r^p • U y)
    (D : ℕ) (hh : ShellBound F D (3+p) v J) :
    ∃ B : S.Field D, ∀ (n : ℕ) (q : Fin n→S.Tag) (x : Points (n+1)), x∈conf _ →
      ∀ χ, Window x χ → flux J χ (fun y => U (y-x 0)) x q v=disc (Fin.cons ⟨D,B⟩ q) x := by
  classical
  choose W hW using fun I : Watch C => exists_window I.held I.distinct
  let A (I : Watch C) := flux J (W I) U I.held (S.classTokens ∘ I.q) v
  have hs (I : Finset (Watch C)) : ∃ B : S.Field D,∀ y∈I,A y=y.tester S D B := by
    let Z := LinearMap.pi (fun y : I => y.val.tester S D)
    obtain ⟨B,hB⟩ := obtainable Z (fun y : I => A y.val) (fun g hx => physical_value hC hq ho H h hc v U hw hl p hg D hh
      (fun y : I => y.val) g hx (fun y : I => W y.val) (fun y => hW _))
    exact ⟨B,fun y hy => (congr_fun hB (⟨y,hy⟩:I)).symm⟩
  obtain ⟨T,hT⟩ := Work.A04.finite_faithful _ (observes H D)
  obtain ⟨B,hB⟩ := hs T
  have hv (I : Watch C) (χ : E4 → ℝ) (hh : Window I.held χ) :
      flux J χ U I.held (S.classTokens ∘ I.q) v = I.tester S D B := by
    obtain ⟨b,hb⟩ := hs (insert I T)
    have ht : b=B := hT (funext (fun y : T => (hb y.val (Finset.mem_insert_of_mem y.property)).symm.trans (hB y y.property)))
    exact (unchanged_flux H h hc v U hw hl _ I.distinct hh (hW I) _).trans (ht ▸ hb I (Finset.mem_insert_self ..))
  refine ⟨B,fun n q x hx χ hχ => ?_⟩
  refine tendsto_nhds_unique_of_frequently_eq (continuous_flux H hx hχ U (fun i => (hw i).continuous) J q v)
    (cont_disc H (Fin.cons ⟨D,B⟩ q) hx).continuousAt ?_
  refine (((meets_grid C x).and_eventually (valid_nearby hx hχ)).mono ?_)
  rintro y ⟨⟨hp,k,w,rfl⟩,_,hz⟩
  obtain ⟨_,s,u,z,rfl,hp',hu,rfl⟩ := raised (C:=C) k hp q
  let I : Watch C := ⟨n,k,z,u,hp'⟩
  rw [← hu] at hz ⊢
  change flux J χ (fun y => U (y - Points.across s I.held 0)) (Points.across s I.held) (S.classTokens ∘ u) v =
    disc _ (Points.across s I.held)
  rw [moves_flux H I.distinct s U J _ v (show Window (Points.across s I.held) χ from hz),
    slide_disc H I.held s I.distinct,show (fun y => U (y-I.held 0)) = U from funext fun y => by rw [I.origin,sub_zero]]
  exact (hv I _ (moves_window s hz)).trans (Watch.test_known _ _)
end ground
end YM.Next.UVStress
