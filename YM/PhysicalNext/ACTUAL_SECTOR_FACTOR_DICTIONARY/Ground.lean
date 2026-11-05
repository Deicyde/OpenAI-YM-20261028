import YM.Extra.ITERATION_NO_LOSS.Placement
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Audition


/-!
# Basis of the actual orbit

The mask/carrier-dependent exponent logs, tag probabilities etc of a
component product should compare to this normalization. Need this even
for a marker on a K with vacuum coefficient zero, hence the computation
at the mere `R.exponent`, WITHOUT factoring such a marker by R.eval.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Ground
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open AnalyticBridge.Sharp AnalyticBridge.Sharp.Almanac
open AnalyticBridge.LocalGaussian Spot
open Wires Geo Notify Voice Voice.Check Parcel Shipment
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (D : AnalyticBridge.LocalGaussian.Desk G S) (h : Lit D) (F : Forest S.ratio) (k₀ k : S.Choices) (V : Config G c) (A : Stores S)
    (hA : A.flags= RG.flags (temp D.betaHat) V)
local notation "x₀"=> D.betaHat
local notation "T₀"=> D.tube
local notation "R₀"=> D.input
local notation "L₀"=> stars D F k₀
local notation "H₀"=> chosen D F k₀ A k
open scoped YM.Push.SectorMeasure

private lemma base_rows (n : ℕ) (U : Config G f) : D.input.path.inChannels D.input.clip D.input.p D.input.beta U =
      averaged (fun s => reduced D.input n (pull s 0 U)) + D.input.beta * cutR D.input n U := by
  let q (s : Signed) := ∑ i, crown D.input.path D.input.clip n 1 D.input.p.threshold (pull s 0 U) i
  have hk (s : Signed) : D.input.path.principal D.input.clip D.input.p D.input.beta (pull s 0 U) =
      reduced D.input n (pull s 0 U) + D.input.beta * q s := by
    simp only [PathData.principal,q,reduced,cuff,Finset.sum_sub_distrib,mul_sub,mul_add]; abel
  change averaged _=_
  simp_rw [hk]; rw [av_add]; unfold q cutR averaged; rw [← Finset.mul_sum]; ring

private lemma landscape (R : Rep G f) (T : Tube G S) (x : ℝ) (h : Fits T R x)
    (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c) (hm : S.patch.Branches S.kernel G) :
    S.likelihood U k * S.noise R.beta (S.prediction U k) V =
      S.likelihood U k * (sieve T R.beta x V * prefactor S G R.beta *
      Real.exp (R.beta*cutR R (till x) U - R.beta * Rows.fee T x V k A U)) := by
  let C:=averaged fun s=>∑ i,crown T.down T.low (till x) S.patch.L.val (temp x) (pull s 0 V) i
  let e:=cutR R (till x) U
  have hl : wholeGap T x U V=e-C := by
    unfold wholeGap crownGap e C cutR; rw [h.path,h.clip,h.temp]; exact av_sub ..
  let book:=Rows.fee T x V k A U
  have he : enters T R.beta x k V U=prefactor S G R.beta*S.likelihood U k* Real.exp (-R.beta*book) := by
    rw [enters_eq hm A]; unfold leaves book Rows.fee; rw [mul_add,Real.exp_add]; ring
  have hf : sieve T R.beta x V=Real.exp (-R.beta*C):=rfl
  unfold enters taggedKernel at he; rw [hl] at he
  rw [hf]; change _=_ * (_ * _ * Real.exp (R.beta*e-R.beta*book))
  calc
    _ = (S.likelihood U k * S.noise R.beta (S.prediction U k) V * Real.exp (-R.beta*(e-C))) * Real.exp (R.beta*(e-C)) := by
      rw [mul_assoc (S.likelihood .. * _), ← Real.exp_add]; ring_nf; simp
    _ = _ := by
      rw [he]
      rw [show S.likelihood U k*(_ * prefactor .. * _)=(prefactor S G R.beta*S.likelihood U k)*(Real.exp (-R.beta*C) *Real.exp (R.beta*e-R.beta*book)) by ring]
      rw [mul_assoc (prefactor .. * _),← Real.exp_add,← Real.exp_add]; ring_nf

/-- Linearized currency for arbitrary real or complex column (Bochner
normalizations remain in `Almanac.body`). -/
def staple (k : S.Choices) (V : Config G c) (A : Stores S) (p : Room G x₀ F A) : ℝ :=
    (L₀).body V A k (fun _ _=>1) p

lemma real_body (g : AnalyticBridge.Sharp.ReadAt S G) (p : Room G x₀ F A) :
    (L₀).body V A k g p= g k ((H₀).hard V p) * staple D F k₀ k V A p := by
  have hf := (L₀).adjusted_body V A k (fun _ _=>1) g p
  simp only [mul_one] at hf; exact hf

/- Carrier equality with all K tables untouched. No all-field V
claim in assembled form. -/
include h hA
lemma initial (P : Room G x₀ F A) :
    (L₀).body V A k (fun _ U=>Real.exp (D.input.exponent U)) P =
      (∏ j:(H₀).TestIndex,Spot.test H₀ V P j) * Real.exp ((H₀).sumValue V P) := by
  obtain ⟨P₀,hP⟩:= h.valid.funds; obtain ⟨n,b,h₁,h₂⟩:=hP.feeds
  let x := D.betaHat; let J:=D.chart; let r := D.radius; let q:=D.broadCut
  let T:= D.tube; let R:= D.input; let β:=R.beta
  let U:= (H₀).hard V P
  let a:= (H₀).material V P
  let C:= (H₀).C V; let m:= (H₀).m V P.1
  let g:=D.g
  let l:=S.likelihood U k; let v:=A; let d:=D.allocation.bill A k U V; let e:=prefactor S G β
  let s:=sieve T β x V; let t:= cutR R (till x) U
  let book:=Rows.fee T x V k A U
  let c:=coarseTail T x D.out V β; let w:= averaged fun s=> reduced R (till x) (pull s 0 U); let p:= R.activities.additive R.p U
 
  let K:=banker T D.out V β; let V₀:= (R.v*(Fintype.card (Site f):ℝ)); let L:= (H₀).bolt V P; let N:= (Fintype.card S.Choices:ℝ)
  let M:= (H₀).receipt V; let F0:= Real.exp (Next.SectorChange.Gaussian.force C P.2/2)
  let b:=guide T x V k (shots S x) A F q r P.1 a
  have he : book=averaged L+b := (exact_fee T x V k A U).trans (compose_residual T x V k (shots S x) A F q r P.1 h₁ U a)
  have ht : (H₀).affinity V P= Next.SectorChange.Gaussian.force C P.2 /2 - b/g^2 := adjusted T x V k (shots S x) A F q r P.1 C m P.2 (coupling_pos h.valid.betaPos)
  have hg : b/g^2=β*b := by unfold g Desk.g β R; rw [div_eq_mul_inv,by_coupling h.valid.betaPos]; ring
  let y := tape a; let D' := reserve q J r y; let B' := doors q r y
  have hy : Real.exp (∑ i,(H₀).lacquer V P i)=D' := by rw [Real.exp_sum]; rfl
  have hq : (H₀).sumValue V P=(∑ i,(H₀).lacquer V P i)+ M -β*book + Next.SectorChange.Gaussian.force C P.2/2-w+c-p := by
    rw [he]; unfold Spot.sumValue; rw [ht,hg]
    unfold back; change -β*_ + (_ +(M+(Next.SectorChange.Gaussian.force C P.2/2-β*b+((-w+c)+ -p))))=_; unfold L; ring
  rw [Spot.checked_at H₀ V (show (H₀).Flags V from hA), hq]
  have hx : Real.exp ((∑ i,(H₀).lacquer V P i)+ M -β*book + Next.SectorChange.Gaussian.force C P.2/2-w+c-p)=
      D'*Real.exp M * Real.exp (-β*book)*F0* Real.exp (-w)* Real.exp c* Real.exp (-p) := by
    rw [← hy]; unfold F0
    simp_rw [←Real.exp_add]; ring_nf
  rw [hx]
  change (N* Real.exp M*(K*Real.exp V₀*e)⁻¹)*(F0*((D'*B')*((d*l)*(S.noise β (S.prediction U k) V*Real.exp (R.exponent U)))))= N*(B'*d*l)*_
  rw [show R.exponent U=V₀-(w+β*t)-p by change _-_ -_ = _; rw [base_rows D],
    show (d*l)*(S.noise β (S.prediction U k) V*_)=d*(l*S.noise β (S.prediction U k) V)*Real.exp (V₀-(w+β*t)-p) by ring,
    show l*S.noise β (S.prediction U k) V=l*(s*e*Real.exp (β*t-β*book)) from landscape R T x h.valid.same A U k V h.aperture.branched,
    show s=K*Real.exp c from convert_full T x V D.out β h.valid.coarse]
  have hX : Real.exp (β*t-β*book)*Real.exp (V₀-(w+β*t)-p)=Real.exp V₀*(Real.exp (-β*book)*Real.exp (-w)*Real.exp (-p)) := by simp_rw [← Real.exp_add]; ring_nf
  have hβ : e≠0 := (prefactor_pos _).ne'; have hs : K≠0 := (Real.exp_pos _).ne'
  field_simp
  rw [mul_sub, mul_assoc (N * F0 * D' * B' * d * l) (Real.exp ..),hX, neg_mul]; ring
end YM.PhysicalNext.Dictionary.Ground
