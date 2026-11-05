import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Jacobi
import YM.Push.STATIONARY_UNIFORM.Paths


/-! # Real uncut off-coordinate ratio (kinetic estimates)
The denominator is one product in the joint variables. Bounds
orthonormal including rep dimension via physical coords; no
period in this germ estimate. Needed also without proving
RChart windward.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Liquid
open Work.F03 Next.Fluctuations Pressure Jacobi   Function Lattice Gauge Finset RG Push.Uniform Filter Wilson Precision Bid Tree Matrix Exterior
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f : Side} {p : Ratio c f} {B : Forest p}

-- individual dose with the exact Key B G from thermal
def droplet (x : B.Free) : Positions (Joint B G) →L[ℝ] G.Color :=
  ContinuousLinearMap.proj (φ:=fun _:B.Free=>G.Color) (R:=ℝ) x ∘L
    (ContinuousLinearMap.snd ℝ (fieldDir G c 1) (AxisChart G B) ∘L (paint B G).toContinuousLinearMap)
lemma droplet_apply (b : B.Free) (v : Positions (Joint B G)) (j : G.ColorIndex) : droplet b v j=v (Sum.inr (b,j)) := rfl
lemma dry (b : B.Free) (h : Primary c G) : droplet b (bolt (Sum.inl h))=0 := by
  ext i; rw [droplet_apply]; simp [bolt]
lemma dry' (b : B.Free) (h : Key B G) (hx : b≠h.1) : droplet b (bolt (Sum.inr h))=0 := by
  ext i; rw [droplet_apply]; obtain ⟨h,j⟩:=h; dsimp only at hx; simp [bolt,hx]
lemma light (h : Key B G) : ‖droplet h.1 (bolt (Sum.inr h))‖=1 := by
  obtain ⟨h,i⟩ := h
  let b := EuclideanSpace.basisFun G.ColorIndex ℝ
  rw [show droplet h (bolt (Sum.inr (h,i))) = b i by
    ext j; rw [droplet_apply]; by_cases H : j=i <;> simp [H,b,bolt], OrthonormalBasis.norm_eq_one]

variable {O : ChartRatio G}
local notation "σ" => Real.log ∘ O.J
-- germ equality nonzero at flat; also when no free
lemma tincture (he : LocalRatio O) : ContDiffAt ℝ ω σ (0:G.Color) :=
    (he.germ _ (Metric.mem_ball_self he.patch)).log (he.anchored.symm ▸ one_ne_zero)
lemma touch (he : LocalRatio O) (x : B.Free) (v w : Positions (Joint B G)) :
    blade v (σ ∘ droplet x) 0=blade (droplet x v) σ 0 ∧
      mixed v w (σ ∘ droplet x) 0=mixed (droplet x v) (droplet x w) σ 0 := by
  let D := droplet x (G:=G)
  have hp := tincture he
  rw [← map_zero D] at hp
  have h (s : G.Color→ℝ) (j : Positions (Joint B G)) (t) (hg : ContDiffAt ℝ ω s (D j)) : blade t (s ∘ D) j=blade (D t) s (D j) := by
    unfold blade; rw [fderiv_comp _ (hg.differentiableAt (by simp)) D.differentiableAt,D.fderiv]; rfl
  have ht : blade w (σ ∘ D) =ᶠ[𝓝 0] blade (D w) σ ∘ D := by
    filter_upwards [D.continuous.continuousAt.tendsto.eventually (hp.eventually (by simp))] with z hz; exact h _ z w hz
  constructor
  · simpa only [D,map_zero] using h _ (0 : Positions (Joint B G)) v hp
  change blade v (blade w (σ ∘ D)) 0=_
  rw [show blade v _ _=blade v (blade (D w) σ ∘ D) 0 from congr_arg (fun L : Positions (Joint B G)→L[ℝ] ℝ=>L v) ht.fderiv_eq,h _ _ _ (smooth _ hp)]; rw [map_zero]

lemma summable_stroke {ι : Type*} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {S : Finset ι} {F : ι → X → ℝ} {x : X}
    (v w : X) (h : ∀ i∈S, ContDiffAt ℝ ω (F i) x) :
    mixed v w (fun y => ∑ i∈S, F i y) x=∑ i∈S,mixed v w (F i) x := by
  have he : blade w (fun y=>∑ i∈S,F i y) =ᶠ[𝓝 x] fun y=>∑ i∈S,blade w (F i) y :=
    ((eventually_all_finset S).2 (fun i hi=>(h i hi).eventually (by simp))).mono (fun _ hy=> series w hy)
  unfold mixed; rw [show blade v (blade w _) x=blade v (fun y=>∑ i∈S,blade w (F i) y) x from congr_arg (fun p : X→L[ℝ] ℝ=>p v) he.fderiv_eq]
  exact series v (fun i hi=>smooth _ (h i hi))

def bead (u : ChartRatio G) (z : Positions (Joint B G)) := ∑ i : B.Free, ((Real.log ∘ u.J) ∘ droplet i) z
lemma water (he : LocalRatio O) (x : B.Free) : ContDiffAt ℝ ω (σ ∘ droplet (G:=G) x) 0 := by
  let D := droplet x (G:=G); have hp := tincture he; rw [← map_zero D] at hp
  exact hp.comp (f:=D) _ D.contDiff.contDiffAt
lemma hydrated (he : LocalRatio O) : ContDiffAt ℝ ω (bead (B:=B) O) 0 :=
  ContDiffAt.sum fun i _=> water he i

-- one color kind, literals orientations basis not coordinate sums!
def aqueous (u : ChartRatio G) := ‖fderiv ℝ (Real.log ∘ u.J) 0‖ + ‖fderiv ℝ (fderiv ℝ (Real.log ∘ u.J)) 0‖
lemma aquatic (O : ChartRatio G) : 0 ≤ aqueous O := by unfold aqueous; positivity

lemma thirst (he : LocalRatio O) {r : ℝ} (i j : Joint B G) :
  ‖blade (bolt i) (bead O) 0‖ ≤ aqueous O ∧ ‖mixed (bolt i) (bolt j) (bead O) 0‖ ≤ aqueous O * Decay r (address B G i) (address B G j) := by
  unfold bead
  rw [series _ (fun i _=>water he i),summable_stroke _ _ (fun i _ => water he i)]
  simp_rw [(touch he _ _ (bolt i)).1, (touch he _ _ _).2, iter _ _ (tincture he),iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] -- last maybe simplification
  let y (q : B.Free) (i : Joint B G) := (droplet q (bolt i))
  let L := fderiv ℝ σ 0; let F := fderiv ℝ (fderiv ℝ σ) 0
  change ‖∑ q : B.Free,L (y q i)‖ ≤ _ ∧ ‖∑ q : B.Free,F (y q i) (y q j)‖ ≤ _
  have hc a b : 0 ≤ aqueous O * Decay (n:=f) r a b := mul_nonneg (aquatic _) (decay_pos ..).le
  cases i with
  | inl i => simp_rw [show ∀ q:B.Free,y q (Sum.inl i)=0 from fun q=>dry q i,map_zero]; simpa using And.intro (aquatic O) (hc (address B G (.inl i)) (address B G j))
  | inr i =>
    have hz (x' : B.Free) (t : Key B G) : x'≠t.1 → y x' (.inr t)=0 := dry' _ _
    rw [Finset.sum_eq_single_of_mem i.1 (Finset.mem_univ _) (fun i' _ ht => by rw [hz _ _ ht,map_zero]),
      Finset.sum_eq_single_of_mem i.1 (Finset.mem_univ _) (fun i' _ ht => by rw [hz _ _ ht,map_zero]; rfl)]
    have hh : ‖y i.1 (.inr i)‖=1 := light i
    constructor
    · unfold aqueous; exact (L.le_opNorm _).trans (by rw [hh,mul_one]; exact le_add_of_nonneg_right (norm_nonneg F))
    cases j with
    | inl j => rw [show y i.1 (.inl j) = 0 from dry .., map_zero,norm_zero]; exact hc _ _
    | inr k =>
      by_cases hx : i.1=k.1
      · have ht : address B G (.inr i)=address B G (.inr k) := by change i.1.val.1=k.1.val.1; rw [hx]
        rw [ht,Decay,separation_self, Nat.cast_zero,mul_zero,Real.exp_zero,mul_one]
        apply ((F _).le_opNorm _).trans
        rw [hx,show ‖y k.1 (.inr k)‖=1 from light k,mul_one,← hx]
        exact (F.le_opNorm _).trans (by rw [hh,mul_one]; exact le_add_of_nonneg_left (norm_nonneg _))
      rw [hz _ _ hx,map_zero,norm_zero]; exact hc _ _

lemma join (he : LocalRatio O) : (fun z : Positions (Joint B G) => Real.log (∏ i:B.Free,O.J ((paint B G z).2 i))) =ᶠ[𝓝 0] bead O := by
  have hp : ∀ᶠ z : Positions (Joint B G) in 𝓝 0, ∀ i : B.Free, O.J ((paint B G z).2 i) ≠ 0 := by
    rw [eventually_all]
    intro i
    let D := droplet i (G:=G)
    have hx := he.germ _ (Metric.mem_ball_self he.patch)
    rw [← map_zero D] at hx
    change ∀ᶠ z in 𝓝 0, (O.J ∘ D) z ≠ 0
    exact (hx.comp (f:=D) _ D.contDiff.contDiffAt).continuousAt.eventually_ne (by simp [he.anchored])
  filter_upwards [hp] with z hz; rw [Real.log_prod (fun i _=>hz i),bead]; rfl
end YM.Further.PhysicalPeriodLimitF933.Liquid
