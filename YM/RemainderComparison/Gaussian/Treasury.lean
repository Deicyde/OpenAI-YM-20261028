import YM.RemainderComparison.Gaussian.Canvas

/-!
 # Uncut model approximates central integral on the same probes.

 Accounting *only in b* with Brush transversal, before phase/norm
 re-expression. Taylor at b=0 in the scaled chart, not at running positive beta.
 Uncut integrated ONLY per Gaussian polynomial order. There is no assertion
 about convergence/integrability of any resummed uncut-ζ answer. `runway`
 expenditures p_geo polynomial on each common setup/tail of post costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Germ
open Matrix Filter Function Metric Set ProbabilityTheory MeasureTheory Finset
open Lattice RG Pressure Next.Scheduling Push.AbsoluteSums ConnectedActivityE6 Trace
open Coat PhysicalNext.Repeat Lantern Poll Blaze Brush
open scoped Topology BigOperators Classical NNReal ENNReal ContDiff
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {p q : ℝ→ℝ} {n j m k : ℕ} {v u x D C c d C' M : ℝ}
local notation "ℰ" => ℝ×E
local notation "Ξ" => Poll.Body ι

variable (Q : Matrix ι ι ℝ) (U : ℝ×E → Poll.Body ι → F)
local notation "μ₀" => sweep Q

def coupon (R : ℝ) (x : ℰ) := ∫ z, velvet U R x z ∂μ₀
def warrant (i : ℕ) (x : E) := ∫ z, coefficient (fun x=> U x z) i x ∂μ₀
/-- Truncated polynomial from full Gaussian, including leading means. -/
def early (m : ℕ) := polyeval m (warrant Q U)

section funds
variable [CompleteSpace F] [FiniteDimensional ℝ E]
variable {U} (h : Picture U D v u m C)
include h
omit [CompleteSpace F] in
lemma ink (x : ℰ) (hx : x∈patch E v u) : Meristem (velvet U D) x μ₀ m := by
  apply Relative.test_domination (M:=fun _=> C) (integrable_const _)
       ((show ∀ᶠ i in 𝓝 x, i∈patch E v u from (patch_open ..).mem_nhds hx).mono fun _ hh z=> h.stamp hh z)
       ((show ∀ᶠ i in 𝓝 x, i∈patch E v u from (patch_open ..).mem_nhds hx).mono fun y hh=> h.cut y hh)
lemma holder (x : ℰ) (hx : x ∈patch E v u) : Brush m C 1 (coupon Q U D) x :=
    (ink Q h _ hx).buds (fun _=> C) (integrable_const _) zero_le_one (by simp) (ae_of_all _ fun z=> h.stamp hx z)
omit [CompleteSpace F] [FiniteDimensional ℝ E] in
lemma stamp_integrable (x:ℰ) (hx:x∈patch E v u) : Integrable (velvet U D x) μ₀ :=
    (integrable_const (μ:=μ₀) C).mono' (h.cut _ hx).aestronglyMeasurable (ae_of_all _ fun z=> (h.stamp hx z).bound)

lemma inspect (i:ℕ) (hi:i ≤ m) (he:0<v) (x:E) (hx:‖x‖<u) :
    coefficient (coupon Q U D) i x=∫ z in closedBall 0 D, coefficient (fun x=> U x z) i x ∂μ₀ := by
  have hx : (0,x)∈ patch E v u := (patch_test ..).2 ⟨(norm_zero).trans_lt he,hx⟩
  have hp := (ink Q h _ hx).calls.2 i hi
  let Y:=closedBall (0:Ξ) D
  let f :=JetF (velvet U D) i (0,x)
  let L:= ContinuousMultilinearMap.apply ℝ (fun _:Fin i=>ℰ) F (fun _=> (1,0))
  have hh : coefficient (coupon Q U D) i x=(i.factorial:ℝ)⁻¹ • L (∫ z,f z ∂μ₀):= by
    unfold coefficient plain; rw [show iteratedFDeriv ℝ i (coupon Q U D) (0,x)=_ from hp.2]; rfl
  rw [hh,← L.integral_comp_comm hp.1,← integral_smul,← integral_indicator measurableSet_closedBall]; apply integral_congr_ae
  filter_upwards with z; by_cases H:z∈Y
  · rw [indicator_of_mem H]; exact congr_arg (fun f : ℰ→F=> coefficient f i x) (show (fun y=> velvet U D y z)=_ from funext fun _=> indicator_of_mem H _)
  rw [indicator_of_notMem H]; suffices H:L (f z)=0 by rw [H,smul_zero]
  suffices H : f z=0 by rw [H]; exact map_zero _
  unfold f JetF; rw [show (fun y=> velvet U D y z)=(fun _ : ℰ=> (0:F)) from funext fun y=> indicator_of_notMem H _]; cases i with
  | zero => ext; simp
  | succ i=> rw [iteratedFDeriv_succ_const]; rfl
end funds

section wide
variable [CompleteSpace F] [FiniteDimensional ℝ E]
variable {U} (h : Cloud U D v u n m C) (hp : Q.PosSemidef) (hv : Contract Q c) (hh : (Fintype.card ι:ℝ) ≤ M)
local notation "ℑ" => (fun (x : E) z=> coefficient (fun x=> U x z) k x)
local notation "€" => (fun z:Ξ=> C * vat m z)
include hp hv hh h
lemma budget (x : E) (hx : ‖x‖ < u) (he : k ≤ n) (s : Set Ξ) : Integrable (fun z=> coefficient (fun x=> U x z) k x) μ₀ ∧
    ∀ j : ℕ,j+k ≤ n → Brush j (∫ z in s,C*vat m z ∂μ₀) 1 (fun x=> ∫ z in s, coefficient (fun x=> U x z) k x ∂μ₀) x := by
  let W (x:E) z:= ℑ x z
  let Y:=ball (0:E) u; have hu:x∈ Y:= mem_ball_zero_iff.mpr hx
  have hK:Integrable € μ₀:= (charges Q hp hv hh m).1.const_mul _
  have hz i (hi:i ∈ Y) : StronglyMeasurable (W i) := h.fine (mem_ball_zero_iff.mp hi) he
  have hf (j:ℕ) (i:E) (hi : i∈Y) z (hj : j+k ≤ n) : Brush j (€ z) 1 (fun x=> W x z) i:=
    sample ((h.view i (mem_ball_zero_iff.mp hi) z).smaller hj)
  refine ⟨hK.mono' ((hz x hu).aestronglyMeasurable) (ae_of_all _ fun z=> (hf 0 x hu z (by omega)).bound),?_⟩
  intro j hj
  have hp : Meristem W x ((μ₀).restrict s) j := Relative.test_domination hK.restrict
    ((show ∀ᶠ i in 𝓝 x, i∈Y from isOpen_ball.mem_nhds hu).mono fun i hi z=> hf j i hi z hj)
    ((show ∀ᶠ i in 𝓝 x, i∈Y from isOpen_ball.mem_nhds hu).mono fun i hi=> hz i hi)
  exact hp.buds _ hK.restrict zero_le_one le_rfl (ae_of_all _ fun z=> hf j x hu z hj)
lemma care (x:E) (hx: ‖x‖<u) (he:j+k ≤ n) : Brush j (C*lump m c M) 1 (warrant Q U k) x := by
  have hf:= budget Q h hp hv hh x hx (show k≤n by omega) Set.univ|>.2 j he; simp_rw [setIntegral_univ] at hf
  apply hf.climb _ le_rfl; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (charges Q hp hv hh m|>.2) h.expense
lemma discrepancy (x : E) (hx: ‖x‖<u) (he : 0 < v) (hi : j+k ≤ n) :
    Brush j (∫ z in (closedBall (0:Ξ) D)ᶜ, C*vat m z ∂μ₀) 1
      (fun x=> coefficient (coupon Q U D) k x- warrant Q U k x) x := by
  let Y:=closedBall (0:Ξ) D
  let F x:=∫ z in Yᶜ,ℑ x z ∂μ₀
  have hk y (hy:‖y‖<u) := budget Q h hp hv hh (k:=k) y hy (show k≤n by omega) Yᶜ
  refine ((hk x hx).2 j hi).opposite.shimmy ?_
  filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with y hy
  rw [inspect Q h.toPicture _ (by omega) he _ hy]
  change _ - warrant Q U k y= -F y
  rw [show warrant Q U k y=(∫ z in Y,ℑ y z ∂μ₀)+F y from (integral_add_compl measurableSet_closedBall (hk y hy).1).symm]; abel
end wide

/-!
 Uniform over the *entire family of analytic demands* priced by the same
 polygon/radius, including shared products. Does NOT use this claim on
 arbitrary periods without Quilt. Includes the tensor error charge for
 extending profiles to unrestricted coefficients in these charts; reference
 scale still β-independent fees separate. -/
local notation "α₀" => Access.apron
lemma runway (G:Gauge) (L:Side) (n j k m : ℕ) (hf : Reserve G L p) (hB : Bolt G L q)
    (c d:ℝ) (hd:0<d) (hc:0<c) (h : j+(n+1) ≤ k) :
    ∃ Y : ℝ→ℝ, Reserve G L Y ∧ ∀ᶠ t in atTop, let A:=Access.apron G L t; let D:=Sienna.wick G L d t
      ∀ β, inBand (betaF G t L) β → ∀ (u:ℝ) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
       (F:Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopology F] [CompleteSpace F]
       (ι:Type) [Fintype ι] [DecidableEq ι] (_h:(Fintype.card ι:ℝ) ≤ q t) (S₀ : Matrix ι ι ℝ) (_ : S₀.PosDef) (_ : Contract S₀ c)
       (U : ℝ×E→ Poll.Body ι→ F) (_ : Cloud U D A u k m (p t)) (w:E), ‖w‖ < u →
        let g:=gStep β
        Brush j (g^(n+1) * Y t) 1 (fun x=> coupon S₀ U D (g,x) - early S₀ U n (g,x)) w ∧
           ∀ l i,l + i ≤ k → Brush l (Y t) 1 (warrant S₀ U i) w := by
  let C₀:=(n+1:ℕ); let r:ℝ:=-(n+3:ℕ)/2 -- edit
  let t x:=p x + (C₀:ℝ)
  let z x:= p x*lump m c (q x)
  let f x:= t x+z x; refine ⟨f,(hf.add (Reserve.const _)).add (hf.mul (lump_cost _ (Reserve.covers hB) _)),?_⟩
  filter_upwards [night hf hB hc hd r m, Access.exchange (G:=G) (L:=L) r C₀ (by unfold r C₀; push_cast; linarith) Rate.power, Access.wide hf.rate, Delay.shift_pos G L] with x ht hx he hz A D β hβ u E _ _ _ H _ _ _ _ ι _ _ hp S₀ hw hy U hU w hW
  intro g; obtain ⟨hA,hV⟩:= he.2 β hβ
  have hG : 0<g:= hA; have hP: 0 ≤ p x:= hU.expense
  have hv : ((∫ i in (closedBall (0:Poll.Body ι) D)ᶜ, p x * vat m i ∂sweep S₀)) ≤ g^(n+1):= (ht ι S₀ hp hP hw hy).trans ((le_abs_self _).trans (hx β hβ))
  have hε : ‖g‖ < A := by rw [Real.norm_of_nonneg hG.le]; exact hV
  have hb : (g,w)∈patch E A u:= (patch_test ..).2 ⟨hε,hW⟩
  have hl (l i:ℕ) (hi : l+i ≤ k) : Brush l (z x) 1 (warrant S₀ U i) w := care S₀ hU hw.posSemidef hy hp _ hW hi
  have hZ: 0 ≤ z x:= (hl 0 0 (Nat.zero_le _)).nonneg
  let V:=coupon S₀ U D; let V' := trunc n V; let W:=early S₀ U n; let y:= g^(n+1)
  have hf:= Trace.vertically V n ((show ∀ᶠ i in 𝓝 (g,w), i∈patch E A u from (patch_open ..).mem_nhds hb).mono fun i hi s hs=> (holder S₀ hU.toPicture _ (keeps hi hs)).smaller h)
  have he' : ‖g‖ ≤ 1:= (hε.trans (he.1.2.1.trans he.1.2.2.1)).le
  have hX : Brush j (C₀*y) 1 (fun i=> V' (g,i)-W (g,i)) w :=
    Trace.fareval (a:=coefficient V) he' fun l hl=> (discrepancy S₀ hU hw.posSemidef hy hp _ hW he.1.1 (by omega : j+l ≤ k)).climb hv le_rfl
  have hT : 0 ≤ t x:=add_nonneg hP (Nat.cast_nonneg _)
  refine ⟨((hf.gathering hX).climb ?_ le_rfl).shimmy ?_,fun l i hi=> (hl l i hi).climb (le_add_of_nonneg_left hT) le_rfl⟩
  · rw [abs_of_pos hG]; change y*p x+ _ ≤ y*(t x+z x)
    have hh : (C₀:ℝ)*y=y*C₀:=mul_comm ..
    rw [hh,← mul_add]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hZ) (pow_pos hG _).le -- edit
  exact Eventually.of_forall fun i=> by change V _ - W _= (V (g,i)-V' (g,i))+(V' _-W _); abel

end YM.RemainderComparison.Germ
