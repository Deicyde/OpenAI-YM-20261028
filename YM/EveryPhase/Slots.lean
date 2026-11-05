import YM.EveryPhase.Tensor

/-! # Absolute coordinates on insertion strips -/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Boundary Next.BOUNDARY Mink Complex WithLp
open scoped Topology BigOperators
variable {n : ℕ} {A : Type*}

def pair (k : Fin n) : NearPair (n+1) := ⟨k.castSucc,k.succ,rfl⟩
-- abbreviate nondependent insertNth
def hole (j : Fin (n+1)) (x : Fin n → A) (a : A) : Fin (n+1) → A := j.insertNth a x
@[simp] lemma hole_self (j : Fin (n+1)) (x : Fin n → A) (a) : hole j x a j=a := Fin.insertNth_apply_same ..
@[simp] lemma hole_next (j : Fin (n+1)) (x : Fin n → A) (a) (k : Fin n) : hole j x a (j.succAbove k)=x k := Fin.insertNth_apply_succAbove ..
lemma first_slot (k : Fin n) : k.succ.succAbove k=k.castSucc := Fin.succAbove_of_succ_le _ _ le_rfl
lemma second_slot (k : Fin n) : k.castSucc.succAbove k=k.succ := Fin.succAbove_of_le_castSucc _ _ le_rfl

lemma switch_hole (k : Fin n) (x : Fin n → A) (a) : hole k.succ x a ∘ (pair k).s=hole k.castSucc x a := by
  funext j
  refine Fin.succAboveCases k.castSucc ?_ ?_ j
  · simp [pair,NearPair.s] 
  intro l
  change hole _ x a (Equiv.swap k.castSucc k.succ (k.castSucc.succAbove l))=_
  rw [hole_next]
  by_cases h : l=k
  · subst l; rw [second_slot,Equiv.swap_apply_right,← first_slot, hole_next]
  have he : k.castSucc.succAbove l=k.succ.succAbove l := by
    rcases lt_or_gt_of_ne h with hh|hh
    · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hh),
        Fin.succAbove_of_succ_le _ _ (Fin.succ_le_succ_iff.mpr hh.le)]
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hh.le),
      Fin.succAbove_of_lt_succ _ _ (Fin.succ_lt_succ_iff.mpr hh)]
  have h1 : k.castSucc.succAbove l ≠ k.castSucc := Fin.succAbove_ne _ _
  have h2 : k.castSucc.succAbove l ≠ k.succ := by rw [he]; exact Fin.succAbove_ne _ _
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, he,hole_next]


def seat (j : Fin (n+1)) (x : Points n) (y : E4) := points (hole j (fun i => x i) y)

@[simp] lemma seat_seat (j : Fin (n+1)) (x : Points n) (y) : seat j x y j=y := hole_self ..
@[simp] lemma seat_next (j : Fin (n+1)) (x : Points n) (y) (l) : seat j x y (j.succAbove l)=x l := hole_next ..
def cushion (j : Fin (n+1)) : WithLp 2 (Points n × E4) ≃ₗᵢ[ℝ] Points (n+1) where
  toFun p := seat j p.fst p.snd
  invFun x := toLp 2 (points (fun i => x (j.succAbove i)), x j)
  left_inv p := by apply ofLp_injective 2; apply Prod.ext <;> simp
  right_inv p := by apply PiLp.ext; intro i; refine Fin.succAboveCases j ?_ ?_ i <;> simp
  map_smul' c p := by apply PiLp.ext; intro i; refine Fin.succAboveCases j ?_ ?_ i <;> simp
  map_add' p q := by apply PiLp.ext; intro i; refine Fin.succAboveCases j ?_ ?_ i <;> simp
  norm_map' p := by
    change ‖seat j p.fst p.snd‖=‖p‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2 _ p.fst,
      Fin.sum_univ_succAbove _ j]
    simp [add_comm]

def chairs (j : Fin (n+1)) : (Points n × E4) ≃L[ℝ] Points (n+1) :=
    (prodContinuousLinearEquiv 2 ℝ (Points n) E4).symm.trans (cushion j).toContinuousLinearEquiv
lemma chairMeasure (j : Fin (n+1)) : MeasurePreserving (chairs j) :=
    (cushion j).measurePreserving.comp (WithLp.volume_preserving_toLp _ _)

/-- real spatial arguments throughout. -/
def laid (x : SpacePoints n) (u : Times n) := glow (place x (fun i => (u i).re)) (dawn (fun i => (u i).im))
def lay (r : Space3) (z : ℂ) (a : Axis) : ℂ := if a=timeAxis then z else (position r 0 a : ℂ)
lemma lay_real (r : Space3) (t : ℝ) (a : Axis) : lay r t a=(position r t a:ℂ) := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨i,rfl⟩ | rfl
  · rw [lay,if_neg (Fin.castSucc_ne_last i)]; change (spatial (position r 0) i:ℂ)=(spatial (position r t) i:ℂ); simp
  rw [lay,if_pos rfl]; change _=(YM.time _:ℂ); simp
lemma laid_at (x : SpacePoints n) (u : Times n) (i : Fin n) (a : Axis) : laid x u (i,a)=lay (x i) (u i) a := by
  unfold laid dawn glow place; simp only [Points.flatten_at,points_apply]
  rcases Fin.eq_castSucc_or_eq_last a with ⟨j,rfl⟩ | rfl
  · rw [lay,if_neg (Fin.castSucc_ne_last j)]; change (spatial (position (x i) (u i).re) j:ℂ)+ (spatial (position 0 (u i).im) j:ℂ)*I = (spatial (position (x i) 0) j:ℂ)
    simp
  rw [lay,if_pos rfl]; change (YM.time _:ℂ)+ (YM.time _:ℂ)*I = _; simp
lemma laid_inside (x : SpacePoints n) {u : Times n} (h : u∈strict n) : laid x u∈tube n := by
  change shade _∈fields n; rw [laid,im_glow]; exact etched h
lemma laid_place (x : Points n) (u : Heights n) : laid (Boundary.trace x) (shift x u)=glow x (dawn u) := by
  unfold laid shift; simp; congr; exact Work.C20.place_same x

def lodge (j : Fin (n+1)) (x : SpacePoints n) (u : Times n) (r : Space3) (z : ℂ) :=
    laid (hole j x r) (hole j u z)

lemma lodge_name (k : Fin n) (x : SpacePoints n) (u : Times n) (r) (z) :
    (pair k).name (lodge k.succ x u r z)=lodge k.castSucc x u r z := by
  unfold NearPair.name lodge laid dawn
  rw [im_glow,re_glow, ← switch_hole, ← switch_hole]
  congr 1

lemma hole_ord {u : Times n} (j : Fin (n+1)) (z : ℂ) (h : u∈strict n)
    (h1 : ∀ l, j.succAbove l < j → (u l).im < z.im)
    (h2 : ∀ l, j < j.succAbove l → z.im < (u l).im) : hole j u z ∈ strict (n+1) := by
  intro i k
  refine Fin.succAboveCases j ?_ ?_ i
  · refine Fin.succAboveCases j ?_ ?_ k <;> simp
    exact h2
  intro p; refine Fin.succAboveCases j ?_ ?_ k
  · simp; exact h1 _
  intro l he; simp only [hole_next]
  exact h ((Fin.strictMono_succAbove j).lt_iff_lt.mp he)

/-- local uniform strip over exterior complex times. -/
lemma affords {u : Times n} (hu : u∈strict n) (k : Fin n) : ∃ d : ℝ, 0 < d ∧ ∀ᶠ v in 𝓝 u,
    v∈strict n ∧ ∀ (z : ℂ) (s : ℝ), z.im=(v k).im → 0<s → s≤d →
      hole k.succ v (z+s*I) ∈ strict (n+1) ∧ hole k.castSucc v (z-s*I) ∈ strict (n+1) := by
  let H := fun q : Times n × ℝ => ∀ i j : Fin n, i<j → (q.1 i).im + q.2 < (q.1 j).im
  have he : ∀ᶠ q in (𝓝 u) ×ˢ (𝓝 (0:ℝ)), H q := by
    rw [← nhds_prod_eq]; refine eventually_all.mpr (fun i => eventually_all.mpr fun j => ?_)
    by_cases hi : i<j
    · have hf : Continuous (fun q : Times n × ℝ => (q.1 i).im + q.2) := by fun_prop
      have hg : Continuous (fun q : Times n × ℝ => (q.1 j).im) := by fun_prop
      apply Eventually.mono ( (isOpen_lt hf hg).mem_nhds (x := (u,0)) ?_) (fun x hx _ => hx)
      change (u i).im + 0 < (u j).im; rw [add_zero]; exact hu hi
    exact Eventually.of_forall fun _ h => (hi h).elim
  obtain ⟨A,hA,C,hC,h⟩ := mem_prod_iff.mp he
  obtain ⟨d,hp,hd⟩ := ((show ∀ᶠ d in 𝓝[>] (0:ℝ), d∈C from mem_nhdsWithin_of_mem_nhds hC).and (show ∀ᶠ d in 𝓝[>] (0:ℝ), d∈Ioi (0:ℝ) from self_mem_nhdsWithin)).exists
  change 0<d at hd; refine ⟨d,hd,?_⟩
  filter_upwards [hA,(open_strict _).mem_nhds hu] with v hv hw
  refine ⟨hw, ?_⟩
  intro z s hh hs ht
  have he : H (v,d) := h ⟨hv,hp⟩
  change ∀ i j, i<j → (v i).im+d < (v j).im at he
  constructor <;> refine hole_ord _ _ hw ?_ ?_ <;> intro i hi <;> simp [hh]
  · have hj : i≤k := Fin.succ_le_succ_iff.mp ((Fin.succAbove_lt_iff_succ_le ..).mp hi)
    exact lt_of_le_of_lt ((show StrictMono (fun i => (v i).im) from hw).monotone hj) (lt_add_of_pos_right _ hs) 
  · have hj : k < i := Fin.succ_lt_succ_iff.mp ((Fin.lt_succAbove_iff_lt_castSucc ..).mp hi)
    linarith [he k i hj]
  · have hj : i < k := Fin.castSucc_lt_castSucc_iff.mp ((Fin.succAbove_lt_iff_castSucc_lt ..).mp hi)
    linarith [he i k hj]
  have hj : k ≤ i := Fin.castSucc_le_castSucc_iff.mp ((Fin.lt_succAbove_iff_le_castSucc ..).mp hi)
  exact lt_of_lt_of_le (sub_lt_self _ hs) ((show StrictMono (fun i => (v i).im) from hw).monotone hj)

end YM.EveryPhase.Stress
