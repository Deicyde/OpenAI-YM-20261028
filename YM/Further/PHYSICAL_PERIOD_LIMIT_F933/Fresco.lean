import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Dividends
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Enrobe
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Loom


/-!
No contour on V, nor assertion continuation on any strip §Cg2.
Uniform even for small gauge, real directions, nonperiodic trees at output
by using further consumers first to pick canonical. Number of coarse sites,
covering ratio and number of free (physical slice entries) DIFFER, hence keep each until converted.
Keep pre prices & projection tracker V.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Fresco
open Jacobi Macrame Macrame.Lace Polytrace Withdrawal Liquid Enamel Loom Function Lattice Gauge RG Tree Matrix Finset Precision Filter Exterior Bid Wilson Set Metric Push.Uniform Push Shingle Pitch
    Extra.Iteration Extra.Iteration.Calibration
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge}
variable {X Y E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma jolt (L : X→L[ℝ] Y) {Q : Y → E} (h : ContDiffAt ℝ ω Q 0) (u v : X) :
    mixed u v (Q ∘ L) 0=mixed (L u) (L v) Q 0 := by
  have he {Q : Y → E} (x : X) (s) (he : ContDiffAt ℝ ω Q (L x)) : blade s (Q ∘ L) x=blade (L s) Q (L x) := by
    unfold blade; rw [fderiv_comp _ (he.differentiableAt (by simp)) L.differentiableAt,L.fderiv,ContinuousLinearMap.comp_apply]
  have hx : Tendsto L (𝓝 0) (𝓝 0) := map_zero L ▸ L.continuous.continuousAt.tendsto
  have ht : blade v (Q ∘ L)=ᶠ[𝓝 0] (blade (L v) Q ∘ L) := by
    filter_upwards [hx.eventually (h.eventually (by simp))] with y hy; exact he y _ hy
  unfold mixed; rw [show blade u (blade v _) 0=blade u (blade (L v) Q ∘ L) 0 from congr_arg (fun l:X→L[ℝ]E=>l u) ht.fderiv_eq,he _ _ (map_zero L ▸ smooth _ h),map_zero]

lemma gnat (L : X→L[ℝ] Y) {ι : Type} [Fintype ι] {P : Y→ Matrix ι ι ℝ} (H : Faces P 0) (v w : X) :
    delta v (P ∘ L) 0=delta (L v) P 0 ∧ delta v (delta w (P ∘ L)) 0 = delta (L v) (delta (L w) P) 0 := by
  constructor
  · ext i j
    let F y := P y i j
    change fderiv ℝ (F ∘ L) 0 _=fderiv ℝ F 0 _
    have hh : ContDiffAt ℝ ω F (L 0) := map_zero L ▸ H i j
    rw [fderiv_comp _ (hh.differentiableAt (by simp)) L.differentiableAt,map_zero,L.fderiv,ContinuousLinearMap.comp_apply]
  ext i j
  exact jolt L (H i j) _ _

section One
variable {c f : Side} {S : StepData c f} {F : Forest S.ratio} (t : S.Choices) {p : Clip} {R : PathData G} {O : ChartRatio G}
  (ho : LocalRatio O) {g : In G c → AxisChart G F} (he : Critical F p R g)
include t ho he
omit ho he in
private lemma mEq (z : Positions (Joint F G)) :
    Polytrace.determinantLog (Uniform.priced F t p R) z = Real.log (@Matrix.det (Key F G) inferInstance inferInstance ℝ _ (block (Uniform.priced F t p R) z)) := by
  unfold Polytrace.determinantLog
  rw [Subsingleton.elim (fun a b:Key F G=> Classical.propDecidable (a=b)) (inferInstanceAs (DecidableEq (Key F G)))]

theorem port (H : Faces (trend F t p R g) 0) (hv : 0< (trend F t p R g 0).det) (u v : Positions (Primary c G)) :
    let y := Liquid.bead O ∘ curve (Uniform.station g)
    let K := statement (trend F t p R g) y
    ContDiffAt ℝ ω y 0 ∧ ContDiffAt ℝ ω K 0 ∧
      iteratedFDeriv ℝ 2 (determinant F t R p g O ∘ tint G _) 0 ![u,v]=mixed u v K 0 := by
  intro y K
  have ht : Uniform.station g 0=0 := by unfold Uniform.station; simp [he.1]
  let X := curve (Uniform.station g)
  have hh : X 0=0 := by change meetVar 0 _=0; rw [ht]; exact (partSpace _ _).symm.map_zero
  have hs : ContDiffAt ℝ ω X 0 := by
    let V := tint G (Body 1 c)
    apply along
    have h : ContDiffAt ℝ ω g (V 0) := map_zero V ▸ he.2.1
    exact (tint G F.Free).symm.contDiff.contDiffAt.comp (f:=g ∘ V) _ (h.comp (f:=V) _ V.contDiff.contDiffAt)
  have hr : ContDiffAt ℝ ω y 0 := ((hh.symm ▸ (show ContDiffAt ℝ ω (Liquid.bead O) (0 : Positions (Joint F G)) from Liquid.hydrated ho)) : ContDiffAt ℝ ω _ (X 0)).comp (f:=X) _ hs
  -- derive det smooth here not assumed
  have hZ : ContDiffAt ℝ ω K 0 := (contDiffAt_const.mul ((face_det H).log hv.ne')).sub hr
  have hz := Dividends.viewed (t:=t) he ho
  have hE : Dividends.collected F t p R O ∘ X=K := by
    ext1 z; change (1/2:ℝ)*Polytrace.determinantLog _ _-y z=(1/2:ℝ)*Real.log _ -y z
    rw [mEq (p:=p) (R:=R) t]; rfl -- arguments check
  change _=ᶠ[nhds _] _ ∘ X at hz; rw [hE] at hz
  rw [(hz.iteratedFDeriv ℝ _).eq_of_nhds]; exact ⟨hr,hZ,(iter _ _ hZ).symm⟩
end One

variable {c C f F : Side} {P : Patch} {Q : KernelChoices}
    {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {M : ℕ}
    (hC : C.val=c.val*M) (he : 2≤c.val)
    (T : Forest (decreed h)) {U : Forest (decreed H)}
    (cb : (Macrame.Lace.project (h:=h) (H:=H) hC he).Fitted T U)
local notation "L" => Macrame.Lace.project (h:=h) (H:=H) hC he
local notation "S₀" => stepped Q h
local notation "S'" => stepped Q H
local notation "Ψ" => Macrame.Lace.Fitted.narrow L (G:=G)
variable {R : PathData G} {p : Clip} {j N : ℕ} {μ B Λ : ℝ} {A : Push.Uniform.Before G μ B j Q N} {O : ChartRatio G}
    (hK : Larger (G:=G) (stepped Q h)) (hY : Larger (G:=G) (stepped Q H)) (hR : R.Bounds p μ B Λ) (hJ : P.J=j)
    (hN : 4≤N) {u : In G c→ AxisChart G T} (hu : A.Service (S:=stepped Q h) T p R u)
    {v : In G C→AxisChart G U} (hv : A.Service (S:=stepped Q H) U p R v) (ho : LocalRatio O)
include hC he T cb hK hY hR hJ hN hu hv ho

def fuel (Z : ChartPrices) (n : ℕ) := spending Z.coords (punch Z n) (pint Z n) (Z.gap/2/2)⁻¹ (Enamel.glue Z)
def stamp (Z : ChartPrices) := Enamel.glue Z/4/2

local notation "ζ" => A.tables p P
local notation "ν" => Positions (Primary c G)
local notation "μ₁" => Positions (Primary C G)
-- expose post-L price based on SAME Preorder. kernel and operator same on extension Patch.
lemma subscribed (hx : Shelter Ψ cb.track (Uniform.priced (S:=S₀) T (plain Q) p R) (Uniform.priced (S:=S') U (plain Q) p R) (M^4))
    (hr : Reserved (address U G ∘ Sum.inr) cb.track f.val) (i k : Positions (Primary c G)) (hi : ‖i‖≤1) (hk : ‖k‖≤1) :
    let W := determinant (S:=S₀) T (plain Q) R p u O ∘ tint G _
    let V := determinant (S:=S') U (plain Q) R p v O ∘ tint G _
    let b := onpass Ψ
    0 < stamp ζ ∧ 0≤fuel ζ N ∧
    |(↑(M^4):ℝ)*iteratedFDeriv ℝ 2 W 0 ![i,k] - iteratedFDeriv ℝ 2 V 0 ![b i,b k]| ≤ (Fintype.card (Key U G):ℝ) * fuel ζ N * Real.exp (-stamp ζ*f.val) := by
  intro W V b
  let Y := ζ; let d := Enamel.glue Y; let J := (Y.gap/2/2)⁻¹; let α := Enamel.punch Y N; let δ := Enamel.pint Y N
  have hI := (Pitch.pressure Ψ i).trans hi; have hK' := (Pitch.pressure Ψ k).trans hk
  let a := @Uniform.station G c f S₀ T u; let e := @Uniform.station G C F S' U v
  let t := plain Q (h:=h); let w := plain Q (h:=H)
  let X₀:= Enamel.trend (S:=S') U w p R v; let x₀:= Enamel.trend (S:=S₀) T t p R u
  have hu₀ := @Enamel.current G c f S₀ T t j N p R μ B Λ Q A hK hR hJ rfl _ hu hN i k hi hk
  obtain ⟨-,hg,-,-,hG,ht₀,-,-,-⟩:=hu₀
  have hU V W (Hv:‖V‖≤1) (Hw:‖W‖≤1) := @Enamel.current G C F S' U w j N p R μ B Λ Q A hY hR hJ rfl v hv hN V W Hv Hw
  let I := b i; let K := b k
  obtain ⟨hD,-,hZ,hz,h₂,hF,hT,hL,hs⟩ := hU I K hI hK'
  obtain ⟨-,-,-,-,-,-,-,H₂,-⟩:= hU I I hI hI
  have hh := Enrobe.cover_germ Q hC he T cb hu.critical hv hx
  let loc := address U G ∘ (@Sum.inr (Primary C G) _)
  have hM : ∀ᶠ x in 𝓝 0, e (b x) = onpass cb.track (a x) ∧ Every cb.track (X₀ (b x)) (x₀ x) := hh
  let y := Liquid.bead O ∘ curve a
  let z := Liquid.bead O ∘ curve e
  have he : z ∘ b =ᶠ[𝓝 0] fun x => (↑(M^4):ℝ)*y x := by
    filter_upwards [hM] with x hq
    unfold z y; rw [Function.comp_apply,Function.comp_apply,Function.comp_apply]; unfold bead
    let Y (i:T.Free) := Liquid.droplet i (curve a x)
    have hy (i : U.Free) : Liquid.droplet i (curve e (b x))=Y (cb.limb i) := by
      unfold curve; rw [hq.1]; rfl
    change (∑i:U.Free, Real.log (O.J (Liquid.droplet i (curve e (b x)))))=(↑(M^4:ℕ):ℝ) * (∑i:T.Free,Real.log (O.J (Y i))) -- annot 
    have hi := Finset.sum_congr (s₁:=Finset.univ) rfl (fun (i:U.Free) _=>show Real.log (O.J (Liquid.droplet i (curve e (b x)))) = _ from congr_arg (fun c=> Real.log (O.J c)) (hy i))
    rw [hi]; exact (multiplied cb.limb (cb.trees _) (fun i:T.Free=> Real.log (O.J (Y i)))).trans (by rw [nsmul_eq_mul])
  have hp := port (t:=w) ho (hv.critical) h₂ hF I K
  change ContDiffAt ℝ ω z 0 ∧ ContDiffAt ℝ ω (statement X₀ z) 0 ∧ _ = _ at hp
  have hPP := port (t:=t) ho (hu.critical) hG ht₀ i k
  change ContDiffAt ℝ ω y 0 ∧ ContDiffAt ℝ ω (statement x₀ y) 0 ∧ _=_ at hPP
  let F' := X₀ ∘ b
  have hl : Multiplicity loc Y.coords := (town U).comp Sum.inr_injective
  have hJ : 0≤J := (inv_pos.mpr (half_pos (half_pos hg))).le
  have he' : Faces F' 0 := fun i j => (map_zero b ▸ (show ContDiffAt ℝ ω (fun y=>X₀ y i j) 0 from h₂ _ _) : ContDiffAt ℝ ω (fun y=> X₀ y i j) (b 0)).comp (f:=b) _ b.contDiff.contDiffAt
  have hF' : 0<(F' 0).det := by dsimp only [F',Function.comp_apply]; rw [map_zero]; exact hF
  have hz' : F' 0=X₀ 0 := by dsimp only [F',Function.comp_apply]; rw [map_zero]
  have Hs : Sealed loc d (F' 0)⁻¹ J := hz'.symm ▸ hT -- hs clashes rename
  have hq : Faces X₀ 0 := h₂
  have ht := Loom.spinning (K:=Y.coords) (π:=cb.track) hl hx.fold hr hD hZ hz hJ (F:=F') (G:=x₀) he' hG hF'.ne' ht₀.ne'
    (hM.mono fun i hi => hi.2) ((map_zero b ▸ (show ContDiffAt ℝ ω z 0 from hp.1)) |>.comp (f:=b) _ b.contDiff.contDiffAt)
    hPP.1 he Hs i k ((show Jacobi.delta i F' 0 = _ from (gnat b hq i k).1).symm ▸ (show Sealed loc d (Jacobi.delta (b i) X₀ 0) α from H₂)) ((show Jacobi.delta k F' 0 = _ from (gnat b hq k k).1).symm ▸ (show Sealed loc d (Jacobi.delta (b k) X₀ 0) α from hL)) ((show Jacobi.delta i (Jacobi.delta k F') 0 = _ from (gnat b hq i k).2).symm ▸ (show Sealed loc d (Jacobi.delta (b i) (Jacobi.delta (b k) X₀) 0) δ from hs))
  refine ⟨by unfold stamp; change 0<d/4/2; have := (show 0<d from hD); positivity, disburse _ hZ hz hJ hD,?_⟩
  rw [show iteratedFDeriv ℝ 2 W 0 _ = _ from hPP.2.2,show iteratedFDeriv ℝ 2 V 0 _=_ from hp.2.2,← jolt b hp.2.1]
  exact ht
end YM.Further.PhysicalPeriodLimitF933.Fresco
