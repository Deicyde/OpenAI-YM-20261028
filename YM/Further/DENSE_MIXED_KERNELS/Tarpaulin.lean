import YM.Extra.MULTISOURCE_BOUNDS.Columns
import YM.Further.DENSE_MIXED_KERNELS.Banner
import YM.Further.DENSE_MIXED_KERNELS.Commons
import YM.Push.SECTOR_MEASURE.Presented

/-!
# Exact dense marker-column payment, still one letter at a time

Aggregate the true K completions compatible with the markers in the
full-volume support. Root invoice can have cost per compulsory seed
including frozen & path costs: no unbought volume constants. Total exponent
really includes the cut/coarse gap at β FINE. If specializing with different
foreground data (e.g. preoutput clip/loops before reset) use P actually
chosen for that computation and ensure proper family matching externally.
Loss for the common scalar (kept in all species and all components of
trajectory as that same scalar, as e.g. E normalization), if needing the E
flat determinant estimate still have to earn its tested size. Does NOT
assert any choice works after estimating only one orientation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Measure Finset Lattice RG Wilson Pressure Precision Module Tree
open Push.SectorMeasure Next.Fluctuations.Sector Push.AbsoluteSums Corona Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {c f : Side} {G : Gauge} {P : Rep G c} {R : Rep G f} {S : StepData c f} {T : Tube G S}
    {x W γ σ σ' C C' Λ Λ' δ δ' w w' : ℝ}

namespace Throng
open Oriented Streamer

structure Fits (T : Tube G S) (P : Rep G c) (R : Rep G f) (x : ℝ) : Prop extends Presented.Fits T R x where
  rout : P.path = T.down
  side : P.clip = T.low
  awake : P.p.threshold = Pressure.temp x

/-- Base factored out COMMON even when not doing the dense calculation.
μ det estimates independent price ε needed on these `ℓ`. -/
def base (S : StepData c f) (P : Rep G c) (R : Rep G f) (l : ℝ) (V : Config G c) :=
  Real.exp (R.v*Fintype.card (Site f)-R.beta*frames P V-l*Fintype.card (Site c)) * prefactor S G R.beta

def toll (A : Allocation G S x W) (Y : Stores S) (P : Rep G c) (R : Rep G f) (l : ℝ) (i : Keyed S)
    (U : Config G f) (V : Config G c) := A.bill Y i.key U V * Keyed.card S * taggedKernel S R.beta i.key U V *
      Real.exp (R.exponent U) / base S P R l V

def weight (A : Allocation G S x W) (Y : Stores S) (P : Rep G c) (R : Rep G f) (l : ℝ) (J : Finset ℕ)
    (i : Keyed S) (U : Config G f) (V : Config G c) : ℂ := ↑(toll A Y P R l i U V * waiting R J U)

lemma stable (S : StepData c f) (P : Rep G c) (R : Rep G f) (l : ℝ) (V : Config G c) : 0 < base S P R l V :=
  mul_pos (Real.exp_pos _) (prefactor_pos _)


-- This cost does NOT grow with c
def alphabet (P : Patch) : ℝ := (Fintype.card P.FrameTag:ℝ) * Fintype.card P.Points ^ Fintype.card Axis
lemma alphabet_pos (P : Patch) : 0 < alphabet P := mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (pow_pos
    (Nat.cast_pos.mpr Fintype.card_pos) _)

lemma tag_price : Keyed.card S ≤ Real.exp (alphabet S.patch * Fintype.card (Site c)) := by
  have ht : Keyed.card S=alphabet S.patch ^ Fintype.card (Site c) := by
    rw [Keyed.card_eq]; unfold alphabet StepData.Choices StepData.SitesChoice StepData.BondChoice Edge
    simp only [Fintype.card_prod,Fintype.card_fun,Nat.cast_mul, Nat.cast_pow]; simp_rw [mul_pow]; ring
  rw [ht, mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (alphabet_pos _).le (by linarith [Real.add_one_le_exp (alphabet S.patch)]) _

open Pressure.Stores
variable {l m : ℝ} (A : Allocation G S x W) (Y : Stores S)
    (hr : R.Lawful σ C Λ δ w) (hp : P.Lawful σ' C' Λ' δ' w')
    (hβ : 0≤R.beta) (ht : Fits T P R x) (hb : S.patch.Branches S.kernel G)
    (hh : PointCharge T x W γ)
    (hW : 0 ≤ w) (hf : Throng Y x) (he : 0 ≤ m) (hl : l≤m)


def rent (P : Patch) (σ C Λ δ w σ' C' x l β : ℝ) (Q : BudgetPoint) := alphabet P+l +
    (P.L.val:ℝ)^4 * (w + Streamer.total σ C Λ δ (till x) Q β)+β* per σ' C' (till x) P.L.val

def storm (x : ℝ) : ℝ := (↑(4*radiusB x + 1:ℕ):ℝ)^4

def booked (P : Patch) (σ C Λ δ w σ' C' x l β : ℝ) (Q : BudgetPoint) := storm x * rent P σ C Λ δ w σ' C' x l β Q

include hr hp ht hβ he hl hW
lemma collector (F : Forest S.ratio) (i : Keyed S) (v : F.Slice G) (V : Config G c) (J : Finset ℕ)
    (q Z : ℝ) (hq : 0≤q) (hn : (Fintype.card (Site c):ℝ) ≤ Z*Y.shares)
    (hQ : q*enters T R.beta x i.key V (F.drape v) / prefactor S G R.beta ≤
      Real.exp (-R.beta*(γ*(fiery G x S.patch.L)^2*Y.shares))) :
    let U:=F.drape v
    let s:= q * Keyed.card S * taggedKernel S R.beta i.key U V * Real.exp (R.exponent U) / base S P R l V
    ‖(↑(s * waiting R J U):ℂ)‖ ≤
      Real.exp ((Z*rent S.patch σ C Λ δ w σ' C' x m R.beta R.p - R.beta*(γ*(fiery G x S.patch.L)^2))*Y.shares) := by
  intro U s; let n : ℝ := Fintype.card (Site c); let f' : ℝ := Fintype.card (Site f)
  let t := R.beta; let p := prefactor S G t; have hv : 0 < p := prefactor_pos _
  have ho := stable S P R l V
  let a := Keyed.card S
  let b := total σ C Λ δ (till x) R.p R.beta
  let Vc := cut P (till x) S.patch.L.val V
  let Uc := cut R (till x) 1 U
  have hG : wholeGap T x U V=Uc-Vc := by
    unfold wholeGap Vc Uc crownGap cut; rw [ht.clip,ht.path,ht.temp,ht.side,ht.awake,ht.rout]; exact av_sub ..
  let y := R.exponent U - R.v*f' + t*Uc
  let L₁ := y + l*n + t*(frames P V - Vc)
  have hs : s=a * (q * enters T t x i.key V U / p)*Real.exp L₁ := by
    unfold s enters; rw [hG]
    unfold base; let c := R.v*f' - t*frames P V-l*n
    let d := taggedKernel S t i.key U V; let z := q
    change z*a*d*Real.exp (R.exponent U)/(Real.exp c*p)=a*(z*(d*Real.exp _)/p)*_
    rw [show c=R.v*f' - t*frames P V-l*n from rfl]
    have hy : -(R.v*f'-t*frames P V-l*n) + R.exponent U= -t*(Uc-Vc)+ L₁ := by unfold L₁ y; ring
    have hu : (Real.exp c)⁻¹*Real.exp (R.exponent U) = Real.exp (-t * (Uc - Vc)) * Real.exp L₁ := by unfold c; rw [← Real.exp_neg,← Real.exp_add, hy,Real.exp_add]
    change z*a*d*Real.exp _ / (Real.exp c*p)=_
    calc
      _ = a*(z*d/p)*((Real.exp c)⁻¹*Real.exp (R.exponent U)) := by ring
      _ = _ := by rw [hu]; ring
  let price := t*(γ * (fiery G x S.patch.L)^2)
  let Vp := per σ' C' (till x) S.patch.L.val
  have heq : f' = S.patch.L.val^4*n := by unfold f' n; rw [site_card,site_card,S.ratio.exact_size]; change (((c.val*S.patch.L.val)^4:ℕ):ℝ)=_; push_cast; ring
  let e := m*n+b*f'+Vp*t*n
  have hL : L₁≤ e := by
    have hx : y ≤ f'*b := receipt hr hβ
    have hz : frames P V - Vc ≤ n*Vp := (abs_le.mp (sways hp S.patch.L.property)).2
    have hn : 0 ≤ n := Nat.cast_nonneg _
    unfold L₁ e; linarith only [hx,mul_le_mul_of_nonneg_right hl hn,mul_le_mul_of_nonneg_left hz hβ]
  have hr' : a * (q * enters T t x i.key V U / p) ≤ Real.exp (alphabet S.patch * n) * Real.exp (-price*Y.shares) := by
    rw [show -price*Y.shares = -R.beta * (γ*(fiery G x S.patch.L)^2*Y.shares) by unfold price t; ring]
    have hp : 0 ≤ enters T t x i.key V U := mul_nonneg (kernel_nonneg ..) (Real.exp_pos _).le
    exact mul_le_mul tag_price hQ (div_nonneg (mul_nonneg hq hp) hv.le) (Real.exp_pos _).le
  have hg : 0≤s := div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hq (Keyed.card_pos _).le)
      (kernel_nonneg ..)) (Real.exp_pos _).le) ho.le
  rw [Complex.norm_real,norm_mul,Real.norm_of_nonneg hg,hs]
  change a*_*Real.exp L₁*‖waiting R J U‖≤_
  apply (mul_le_mul (mul_le_mul hr' (Real.exp_monotone hL) (Real.exp_pos _).le (by positivity)) (preserved hr U).2
    (norm_nonneg _) (by positivity)).trans
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; apply Real.exp_monotone
  let h := rent S.patch σ C Λ δ w σ' C' x m R.beta R.p
  have hE : 0≤h := by
    have ht := Streamer.total_pos f hr hβ (till x); unfold h rent; have hp := alphabet_pos S.patch
    have hv : 0≤Vp := paid_per; unfold Vp at hv; positivity

  change alphabet S.patch*n+ -price*_ + e+f'*w≤(Z*h-price)*_
  have he : alphabet S.patch*n + e + f'*w=h*n := by unfold h rent e b Vp t; rw [heq]; ring
  linarith only [he,mul_le_mul_of_nonneg_left hn hE]

include hf hb hh
lemma owes (F : Forest S.ratio) (i : Keyed S) (v : F.Slice G) (V : Config G c) (J : Finset ℕ) :
    ‖weight A Y P R l J i (F.drape v) V‖ ≤
      Real.exp ((booked S.patch σ C Λ δ w σ' C' x m R.beta R.p - R.beta*(γ*(fiery G x S.patch.L)^2))*Y.shares) := by
  have hn : (Fintype.card (Site c) : ℝ) ≤ storm x * Y.shares := by
    unfold storm; push_cast; have hl : Y.flags.card ≤ Y.shares := le_add_self
    apply le_trans (Nat.cast_le.mpr hf.card); push_cast; rw [mul_comm]; gcongr
  let U := F.drape v
  exact collector Y hr hp hβ ht hW he hl F i v V J (A.bill Y i.key U V) (storm x) (A.nonneg ..) hn
    (full_charge hf T F i.key hb (U:=U) (fun _ hi => F.on_tree v ⟨_,hi⟩) A hh hβ)
end Throng
end YM.Further.DenseMixedKernels
