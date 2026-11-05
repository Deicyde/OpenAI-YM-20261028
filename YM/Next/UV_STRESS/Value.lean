import YM.Next.UV_STRESS.Annulus
import YM.Work.A02



/-!
# Point comparisons (shell), or annihilator comparisons

Simultaneous along the same budget, only use dense `generic`
for passage from cutoff. Extend the annihilator bound by continuity
*before* integrating -- saves a quadrature lemma and sup error from number
of nodes. Standing on a fixed annulus here. All integrals later supported
on noncollision.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter Analysis Extraction Table Ward Work.A01
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {F : Order} {S : Table C.book} {n k h D d : ℕ}

namespace Watch
variable (I : Watch C)

def tester (S : Table C.book) (D : ℕ) : S.Field D →ₗ[ℂ] ℂ := frontRead (S.classTokens ∘ I.q) I.held D
lemma test_known (v : S.Field D) : I.tester S D v=disc (Fin.cons ⟨D,v⟩ (S.classTokens ∘ I.q)) I.held := front_eval ..

def asked (B : S.Field 4) (v : S.Field d) (y : E4) := disc
    (Fin.cons ⟨4,B⟩ (Fin.cons ⟨d,v⟩ (S.classTokens ∘ I.q))) (Points.cons y I.held)
end Watch

section tests
variable {ι : Type*} [Fintype ι] (I : ι → Watch C)

omit [Fintype ι] in
/-- One class can approximate these tests simultaneously. Don't need bounded
coefficients uniformly as `ε` varies. For convenience we use 2ε. -/
lemma curves_bound (hp : C.Makes) (hC : Cells.CellHyp C F) (ho : F.PointLimits C S)
    (H : S.Hierarchy) (k : ℕ) (hk : ∀ i,(I i).t ≤ k) :
    ∃ A : ι → ℝ, (∀ i,0 ≤ A i) ∧
      ∀ (D h d : ℕ) (T : Axis → Axis → C.book.Ref 4) (B : C.book.Ref d) (e ε : ℝ), NodeBound C F D h k (d:=d) e ε T B →
        0<ε → ∀ i j (m : ℕ) (y : Lattice.Cover), C.S.gridPoint m y ∈ annulus e →
          (∀ a, (I a).point m y∈generic _) →
          ∃ w : S.Field D,∀ a, ‖(e:ℂ)^h * (I a).asked (S.project 4 (T i j)) (S.project d B) (C.S.gridPoint m y)
            -(I a).tester S D w‖ ≤ ε*A a := by
  classical
  choose A hA he using fun i => (I i).planted hp hC k (hk i)
  refine ⟨fun i => 2*A i,fun i => mul_nonneg (by norm_num) (hA i),fun D h d T B e ε hr hε i j m y hw hf => ?_⟩
  obtain ⟨x,⟨P,hx⟩,hy⟩ := hr.live i j m y hw
  obtain ⟨b,hb,Hb,z,hz⟩ := finite_extract (𝓛:=F.fuse) x P hx
  refine ⟨S.project D z,fun a => ?_⟩
  have hm := ((I a).cost_limit m y F (d:=d) (T i j) B ho H hb (hf a) h e (p:=z) hz).norm
  rw [Watch.test_known]; apply le_of_tendsto hm
  apply Eventually.filter_mono hb
  let f (u : ℕ×ℕ) := fragment (C:=C) (d:=d) (D:=D) h e (T i j) B m y u.1 u.2 (x u)
  have ht : ∀ᶠ u : ℕ×ℕ in F.fuse, ∃ hN : k+1≤u.1,
      Cells.Interior ((terrace C.S k hN u.2).chamber 0) (f u) ∧
        (terrace C.S k hN u.2).rootTest (C.beta u.1 u.2) (f u) ≤ ε + ε := hy ε hε
  filter_upwards [ht,he a] with u hu hv
  obtain ⟨hN,H,HL⟩ := hu; obtain ⟨_,q⟩ := hv
  exact (q _ H).trans ((mul_le_mul_of_nonneg_right HL (hA _)).trans_eq (by ring))

private lemma held_open (e : ℝ) : IsOpen (annulus e) := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

lemma avoid_cons (E : Watch C) (y : E4) (h : ∀ (a : Axis) i, E.held i a ≠ y a) : Points.cons y E.held∈generic _ := by
  intro a i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases (fun _ => rfl) (fun j => ?_) j
    simp [Points.cons,Ne.symm (h a j)]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Points.cons,h a i]
  simp only [Points.cons,points_apply,Fin.cons_succ]
  exact fun hi => congr_arg Fin.succ ((show E.held∈generic _ from E.wild) a hi)

/-- Pay on generic nodes only. We can align to fine grids *finer than* the
exterior scale, and no common alignment to k is presumed here. -/
lemma extends_bound (e : ℝ) (f : E4 → ℂ) (hs : ∀ y ∈ annulus e, (∀ i, Points.cons y (I i).held ∈ conf _) → ContinuousAt f y)
    (A : ℝ) (hk : ∀ m (x : Lattice.Cover), C.S.gridPoint m x∈annulus e →
      (∀ i,(I i).point m x∈generic _) → ‖f (C.S.gridPoint m x)‖ ≤ A) :
    ∀ y∈annulus e, (∀ i, Points.cons y (I i).held∈conf _) → ‖f y‖ ≤ A := by
  classical
  have ht (y : E4) (hp : y∈annulus e) (hh : ∀ i, Points.cons y (I i).held∈generic _) : ‖f y‖ ≤ A := by
    let F : Points 1 := points fun _ => y
    let b k := address (C.S.a k) F 0
    let g k := C.S.gridPoint k (b k)
    have he : Tendsto g atTop (𝓝 y) := (show Continuous (fun x : Points 1 => x 0) by fun_prop).continuousAt.tendsto.comp (chosen (S:=C.S) F)
    refine le_of_tendsto (((hs y hp fun i => generic_conf _ (hh i)).tendsto.comp he).norm) ?_
    have hz (i) : ∀ᶠ k in atTop, (I i).point k (b k)∈generic _ := (Work.A02.continuous_cons.continuousAt.tendsto.comp
      (he.prodMk_nhds (tendsto_const_nhds (x:=(I i).held)))).eventually ((genericOpen _).mem_nhds (hh i))
    filter_upwards [he.eventually ((held_open e).mem_nhds hp), eventually_all.mpr hz] with k hh hp using hk k (b k) hh hp
  intro y hy hg
  let p : E4 := WithLp.toLp 2 (fun _ => 1)
  let W (k : ℕ) := y + costHint k • p
  have hP : Tendsto W atTop (𝓝 y) := (by simpa using (cost_clears.smul_const p).const_add y)
  have hz (i : ι) : ∀ᶠ k in atTop, Points.cons (W k) (I i).held ∈ generic _ := by
    have he (a : Axis) j : ∀ᶠ k in atTop,(I i).held j a ≠ W k a := by
      by_cases hu : (I i).held j a=y a
      · rw [hu]
        exact Eventually.of_forall fun k => by
          change y a ≠ y a + costHint k • (1:ℝ); rw [smul_eq_mul, mul_one]; exact ne_of_lt (by have := cost_pos k; linarith)
      exact (((show Continuous (fun v : E4 => v a) by fun_prop).continuousAt.tendsto.comp hP).eventually
        (show {v | (I i).held j a ≠ v} ∈ 𝓝 (y a) from (isOpen_ne_fun continuous_const continuous_id).mem_nhds hu))
    exact (eventually_all.mpr fun i => eventually_all.mpr (he i)).mono (fun k hk => avoid_cons (I i) _ hk)
  apply le_of_tendsto (((hs y hy hg).tendsto.comp hP).norm)
  filter_upwards [hP.eventually ((held_open _).mem_nhds hy),eventually_all.mpr hz] with k hk he using ht (W k) hk he

/-- Pay against any linear combination annihilating the D-fields. -/
lemma pays_current (hp : C.Makes) (hC : Cells.CellHyp C F) (ho : F.PointLimits C S)
    (H : S.Hierarchy) (k : ℕ) (hk : ∀ i,(I i).t ≤ k) (D : ℕ) (g : ι → ℂ)
    (ht : ∀ v : S.Field D, (∑ i : ι, g i * (I i).tester S D v)=0) :
    ∃ A : ℝ, 0≤A ∧ ∀ (h d : ℕ) (T : Axis → Axis → C.book.Ref 4) (B : C.book.Ref d) (e ε : ℝ),
      NodeBound C F D h k (d:=d) e ε T B → 0<ε → ∀ i j y, y∈annulus e → (∀ a,Points.cons y (I a).held∈conf _) →
        ‖∑ a : ι, g a * ((e:ℂ)^h * (I a).asked (S.project 4 (T i j)) (S.project d B) y)‖ ≤ ε*A := by
  classical
  obtain ⟨A,hA,hb⟩ := curves_bound I hp hC ho H k hk
  refine ⟨∑ i, A i*‖g i‖, Finset.sum_nonneg (fun i _ => mul_nonneg (hA _) (norm_nonneg _)),
    fun h d T B e ε hu he => ?_⟩
  intro i j
  let p (a : ι) y := (e:ℂ)^h * (I a).asked (S.project 4 (T i j)) (S.project d B) y
  let f y := ∑ a : ι, g a * p a y
  refine extends_bound I e f (fun y hy hh => ?_) _ (fun m x hx hP => ?_)
  · let F (v : ι) := fun y => Points.cons y (I v).held
    have hv (i) : Continuous (F i) := Work.A02.continuous_cons.comp (continuous_id.prodMk continuous_const)
    have he a : ContinuousAt (fun x => g a * p a x) y := continuousAt_const.mul
      (continuousAt_const.mul ((cont_disc H _ (hh a)).continuousAt.comp (f:=F a) (hv a).continuousAt))
    exact tendsto_finsetSum _ (fun a _ => (he a).tendsto)
  obtain ⟨w,H⟩ := hb D h d T B e ε hu he i j m x hx hP
  let y := C.S.gridPoint m x
  calc
    _ = ‖∑ a : ι, g a*(p a y-(I a).tester S D w)‖ := by
      simp_rw [mul_sub, Finset.sum_sub_distrib,ht, sub_zero]; rfl
    _ ≤ _ := (norm_sum_le ..).trans (by
      rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro a _
      rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (H a) (norm_nonneg _)).trans_eq (by ring))
end tests
end YM.Next.UVStress
