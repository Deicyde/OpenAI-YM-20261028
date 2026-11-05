import YM.Next.FLUCTUATIONS.Bare
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Exterior
import YM.SectorNext.LARGE_FIELD_REMAINDERS.WeakRows
import YM.Work.E04
import YM.Work.E05


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Common per-exterior-row analytic losses. Delay-priced, fixed L.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations  Scales
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure

variable {G : Gauge} {c f n : Side} {S : StepData c f} (T : Tube G S) (A : Stores S)

def weakRadius (D : ℝ) (L : Side) (x : ℝ) := D*(b x)^5 * fiery G x L

def weakLoss (D C τ A J : ℝ) (L : Side) (x : ℝ) : ℝ :=
    let h := weakRadius (G:=G) D L x; let e := widen (till x) h τ; let t := fiery G x L
    (2*(A*t)*(C*h*e) + (A*t)*(C*(A*t)*e)) + J*(2*t)^4

-- Still goes to zero even AFTER β and any fixed extra halo or width powers.
private lemma ld_delay (L : Side) (D C τ A J : ℝ) (hD : 0≤D) (hC : 0≤C) (ht : 0<τ) (hA : 0≤A)
    (hJ : 0≤J) (n : ℕ) :
    Tendsto (fun x => b x^n * y G L x * weakLoss (G:=G) D C τ A J L x) atTop (𝓝 0) := by
  let H x := weakRadius (G:=G) D L x
  let r x := Real.exp (-τ*till x)
  -- y*t² = p². Every monomial either buys a further t or the kernel rate.
  let Y := y G L
  let Q := p G L
  let g := g G L
  let l1 (x : ℝ) := b x^(n+11)*Q x^3*g x
  let l2 (x : ℝ) := b x^(n+5)*Q x^2*r x
  let l3 (x : ℝ) := b x^(n+6)*Q x^3*g x
  let l4 (x : ℝ) := b x^n*Q x^2*r x
  let l5 (x : ℝ) := b x^n*Q x^4*g x*g x
  have h1 : Tendsto l1 atTop (𝓝 0) := tally_g G L ..
  have h2 : Tendsto l2 atTop (𝓝 0) := tail_price G L _ _ ht
  have h3 : Tendsto l3 atTop (𝓝 0) := tally_g G L ..
  have h4 : Tendsto l4 atTop (𝓝 0) := tail_price G L _ _ ht
  have h5 : Tendsto l5 atTop (𝓝 0) := by simpa only [mul_zero] using (tally_g G L n 4).mul (minute G L)
  have hv := (((((h1.const_mul (2*A*C*D^2)).add (h2.const_mul (2*A*C*D))).add
    (h3.const_mul (A^2*C*D))).add (h4.const_mul (A^2*C))).add (h5.const_mul (J*16)))
  simp only [mul_zero, add_zero] at hv
  refine squeeze_zero' ?_ ?_ hv
  · filter_upwards [(year G L).eventually_gt_atTop 0] with x hx
    have hb : 0 ≤ b x := by linarith [size x]
    have hT : 0<fiery G x L := Work.E09.temp_pos hx
    dsimp only [weakLoss,widen,weakRadius]; positivity
  filter_upwards [(year G L).eventually_gt_atTop 0] with x hx
  have hb : 0≤b x := by linarith [size x]
  have hT : 0<fiery G x L := Work.E09.temp_pos hx
  have hH : 0≤H x := by unfold H weakRadius; positivity
  have hw : widen (till x) (H x) τ ≤ b x * H x + r x := by
    unfold widen b r; gcongr; exact Nat.div_le_self _ _
  change b x ^ n * Y x * ((2*(A*fiery _ x L)*(C*(H x)*_) + (A*_)*(C*(A*_)*_)) + J*(2*_)^4) ≤ _
  have hy' : 0≤Y x := hx.le
  calc
    _ ≤ b x ^ n * Y x * ((2*(A*fiery G x L)*(C*(H x)*(b x*H x+r x)) + (A*fiery G x L)*(C*(A*fiery G x L)*(b x*H x+r x))) + J*(2*fiery G x L)^4) := by
      gcongr
    _ = _ := by
      have hy : Y x * g x ^ 2=1 := yg2 G L hx
      have hy (i : ℕ) : Y x * g x^(2+i)=g x^i := by rw [pow_add,← mul_assoc,hy,one_mul]
      change _=2*A*C*D^2*l1 x+2*A*C*D*l2 x + A^2*C*D*l3 x + A^2*C*l4 x + J*16*l5 x
      unfold H weakRadius l1 l2 l3 l4 l5
      rw [show fiery G x L=g x*Q x from fi ..,pow_add,pow_add,pow_add]
      calc
        _ = 2*A*C*D^2*b x^n*b x^11*Q x^3*(Y x*g x^(2+1)) +
            2*A*C*D*b x^n*b x^5*Q x^2*r x*(Y x*g x^2) +
            A^2*C*D*b x^n*b x^6*Q x^3*(Y x*g x^(2+1)) +
            A^2*C*b x^n*Q x^2*r x*(Y x*g x^2) +
            J*16*b x^n*Q x^4*(Y x*g x^(2+2)) := by ring
        _ = _ := by rw [hy 1, hy 2,show Y x*g x^2=1 from yg2 G L hx]; ring

structure WeakTicket (x : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) (loss d : ℝ) : Prop where
  matrixPay : Bid.Allowance d T x V
  base (i : Cell f) (hi : i∉A.limit x) (ε : ℝ) (he : ε∈Set.Icc (0:ℝ) 1) :
    ε*(T.high.direct*toll U i^2/4-‖T.Mv (till x) (temp x) V (i,false)‖^2/2) ≤
      T.workF (till x) U V (fiery G x S.patch.L) (temp x) i
  coarse (i : Cell c) (hi : i ∉ A.outs x) : toll V i ≤ temp x
  clipped (i : Cell c) (hi : i∉A.outs x) : -loss ≤ T.workC (till x) V (temp x) i
  defect (i : Cell c) (hi : i∉A.outs x) :
    -loss ≤ T.workL (till x) U (S.prediction U k) V (temp x) i + T.workD (till x) V (temp x) i

private lemma uniq {A B : Patch} (h : A.L=B.L) (ht : A.J=B.J) : A=B := by cases A; cases B; congr

/-- Issue d even before L. Loss affordable after L and W; same per-anchor rate for
all sectors and both orientations, doesn't depend on chosen T. -/
lemma weak_pre (P : Teller G) : ∃ d : ℝ, 0 < d ∧ ∀ (L : Side) (W : ℝ), 0<W →
    ∃ (loss : ℝ → ℝ), (∀ᶠ x in atTop, 0≤loss x) ∧
      (∀ n : ℕ, Tendsto (fun x => (b x)^n * y G L x * loss x) atTop (𝓝 0)) ∧
      ∀ᶠ x in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x)≤c.val → P.Funds S T →
      ∀ (F : Forest S.ratio) (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c),
      SliceSet S F U → Seeded A U k V x W → Alive S U k → WeakTicket T A x U k V (loss x) d := by
  obtain ⟨d,hd,hD⟩ := Work.E03.answer P
  refine ⟨d,hd,?_⟩
  intro L W hW
  by_cases hlegal : ∃ D : Patch, D.L=L ∧ D.J=P.j ∧ D.Branches P.bind G
  swap
  · refine ⟨fun _ => 0,by simp, fun n => ?_,Eventually.of_forall (fun x c f S T hl hv ht => ?_)⟩
    · simp only [mul_zero]; exact tendsto_const_nhds
    exact False.elim (hlegal ⟨S.patch,hl,ht.atStep,ht.kernel⟩)
  obtain ⟨M,hM,hj,hm⟩ := hlegal
  obtain ⟨C,τ,r,hC,ht,hr,hI⟩ := interior_cost P M hm
  obtain ⟨R,hR,hL⟩ := outside_size P L W hW
  obtain ⟨ξ,hξ,J,hJ,hpJ⟩ := Work.E05.answer P
  obtain ⟨A0,hA,hP⟩ := Work.E04.answer Work.E03.answer P
  let E := weakLoss (G:=G) R C τ A0 J L
  have hx : 0<R := zero_lt_one.trans_le hR
  let l x := weakRadius (G:=G) R L x
  have h0 : Tendsto l atTop (𝓝 0) := by
    have he := (tally_g G L 5 1).const_mul R; rw [mul_zero] at he
    exact he.congr (fun x => by unfold l weakRadius; rw [fi]; ring)
  have hi x : l x ≥ 0 := by
    unfold l weakRadius; have hb : 0≤b x := by linarith [size x]
    have := temp_nonneg (betaF G x L); unfold fiery; positivity
  refine ⟨E,Eventually.of_forall (fun x => ?_),ld_delay L _ _ _ _ _ hx.le hC.le ht hA.le hJ.le,?_⟩
  · dsimp only [E,weakLoss]; have he := hi x
    have hh : 0≤fiery G x L := temp_nonneg _
    unfold l at he; unfold widen; positivity
  filter_upwards [hL,(hpJ L W).late,(hP L W).late, (hD L W).late,
    Work.E01.radiusB_tendsto.eventually_ge_atTop (10*(predReach M+10)), h0.eventually (ge_mem_nhds hr),
    Work.E07.temp_coarse_le G L] with x hQ hu hh hd' hs hf hB
  intro c f S T hl hy hT F A U k V hU hV ha
  have hM' : S.patch=M := uniq (hl.trans hM.symm) (hT.atStep.trans hj.symm)
  have hP1 := hV.plot ha
  have hP2 (H : ∀ {c f : Side}, (S : StepData c f) → Tube G S → Forest S.ratio →
      Stores S → ℝ → Config G f → S.Choices → Config G c → Prop)
      (h : live P L W (@H) x) : H S T F A x U k V := h c f S hl hy T hT F A U k V hU hP1
  obtain ⟨hc,-,he⟩ := hP2 _ hh
  rw [← hl] at hc
  have hv {b : Cell c} := default_output (A:=A) hV (b:=b)
  have hT0 : 0≤temp x := temp_nonneg _
  have hl' : 0≤fiery G x L := temp_nonneg _
  refine ⟨hP2 _ hd',fun i hxi ε hε => workF_lower _ _ _ (default_fine hV hxi) (default_keeps hV _ A0 hc hxi) _ hε,fun _ => hv,fun i hxi => ?_,fun i hxi => ?_⟩
  · apply le_trans ?_ ((hP2 _ hu).middle i (hv hxi))
    dsimp only [E,weakLoss]
    have hg := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT0 hB 4) hJ.le
    apply neg_le_neg
    apply hg.trans (le_add_of_nonneg_left ?_)
    have hw := widen_nonneg (τ:=τ) (till x) (hi x); have hw' : 0 ≤ weakRadius (G:=G) R L x := hi x; unfold l at hw; positivity
  · have ho : i.1∉A.dome (2*radiusB x) := fun hd => hxi (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hd⟩)
    obtain ⟨z,hz1,hz2⟩ := (hQ c f S T hl hy hT F A U V k hU hV ha).2 _ ho
    have H : R*(radiusB x:ℝ)^5*fiery G x S.patch.L ≤ l x := by
      unfold l weakRadius; rw [hl]; gcongr; unfold b; linarith
    have hv1 := fun a h => (hz1 a h).trans H
    have hv2 := fun a h => (hz2 a h).trans H
    let B := 2*radiusB x/5
    have hh : 3*till x + 4 + predReach S.patch ≤ B := by rw [hM']; unfold B till; omega
    have he' (j) := hI c f S T hM' hT k (till x) B hh U V (l x) (hi x) hf (i,j) z hv1 hv2
    have hb (j) : ‖T.vision (till x) (temp x) V j‖ ≤ A0 * fiery G x L := by rw [← hl]; exact he.up _
    have hp : 0≤A0*fiery G x L := by positivity
    have hL := workLD_lower (till x) U V (S.prediction U k) i A0 C (fiery G x L) (temp x) (l x)
      (widen (till x) (l x) τ) hp hb (fun j => ⟨(he' j).1,(he' j).2 _ _ hp hb⟩)
    unfold E weakLoss
    exact le_trans (neg_le_neg (le_add_of_nonneg_right (by positivity))) hL
end YM.SectorNext.Remainder

namespace YM.SectorNext.Remainder
open Filter Lattice Scales
open scoped Topology
set_option autoImplicit false
lemma loss_delay (G : Gauge) (L : Side) (D C τ A J : ℝ) (hD : 0≤D) (hC : 0≤C) (ht : 0<τ) (hA : 0≤A)
    (hJ : 0≤J) (n : ℕ) :
    Tendsto (fun x => b x^n * y G L x * weakLoss (G:=G) D C τ A J L x) atTop (𝓝 0) :=
  ld_delay L D C τ A J hD hC ht hA hJ n
end YM.SectorNext.Remainder
