import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Change


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
`cutEntry` had precisely the truncated output base outside; extract now
the entire base at the output temperature. Reveals the output tails into
the transformed integrand with their signs. Not assuming division by an
interacting partition function. `flat` here will be the *truncated* no-hole
gram on this same tree (to factor out of a subsequent tree average would
want its det independence too; we work at a fixed actual F, see other
file for comparing prices). logdet(I+S), *not* here a formal trace power
series that would need another aperture estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian Rows
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented

open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {w : ℝ}

variable (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (A : Stores S) (R : Rep G f)
  (W : Stencils S) (F : Forest S.ratio) (D : Allocation G S x w) (q : Chi) (J : ChartRatio G) (d : ℝ)

def spare (β : ℝ) := (Real.sqrt (2 * Real.pi * coupling β ^ 2)) ^ Fintype.card G.ColorIndex * J.scale

lemma spare_pos (h : LocalRatio J) {β : ℝ} (hb : 0<β) : 0 < spare J β := by
  have he := coupling_pos hb
  have hi := h.scale
  unfold spare; have := Real.pi_pos; positivity

/-- χ(J) in chartGuard is relative to j(0), not probHaar by itself. -/
lemma scalars_align (C : Gaussian.Table (In x A F (G:=G))) :
    J.scale ^ Fintype.card (Active A x F)*chartCost C (coupling R.beta) =
      spare J R.beta ^ Fintype.card (Active A x F) * Real.sqrt C.det := by
  simp only [chartCost, Fintype.card_prod, spare,mul_pow,← mul_assoc]
  rw [pow_mul',mul_comm (J.scale ^ _)]

def banker (C : BudgetPoint) (V : Config G c) (β : ℝ) :=
  Real.exp (-β * averaged (fun s => ∑ i, T.down.baseTerm T.low C (pull s 0 V) i))

def coarseTail (C : BudgetPoint) (V : Config G c) (β : ℝ) :=
  β * averaged (fun s => ∑ i, Pressure.cuff T.down T.low C S.patch.L.val (till x) (pull s 0 V) i)

/-- Cut sieve reappears by bringing coarse tails in *positive* sign. -/
lemma convert_full (B : BudgetPoint) (β : ℝ) (h : B.threshold = temp x) :
    sieve T β x V = banker T B V β * Real.exp (coarseTail T x B V β) := by
  unfold banker coarseTail Pressure.cuff
  simp_rw [Finset.sum_sub_distrib, h,av_sub,mul_sub]
  unfold sieve; rw [← Real.exp_add]; ring_nf

def sleeves (B : BudgetPoint) (C : Gaussian.Table (In x A F (G:=G))) (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F)) :=
  let u := physical A F V Y (displaced (m Y) (coupling R.beta) z)
  let a := (m Y + coupling R.beta • z)
  let y := tape a
  let P := R.activities
  reserve q J d y * doors q d y * D.bill A k u V * S.likelihood u k * P.gas R.p u *
    Real.exp (-(averaged (fun s => reduced R (till x) (pull s 0 u))) - P.additive R.p u + coarseTail T x B V R.beta -
        R.beta * averaged (Rows.residual T x V k W A F q d Y u a) +
        adjustment T x V k W A F q d Y C (m Y) (coupling R.beta) z)

lemma sleeves_unfold (B : BudgetPoint)
    (C : Gaussian.Table (In x A F (G:=G))) (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (Y : LinkArray G (Frozen A x F)) (z : Prices G (Active A x F)) :
    sleeves T x V k A R W F D q J d B C m Y z = Real.exp (coarseTail T x B V R.beta - R.v * Fintype.card (Site f))*
      dyed T x V k A R W F D q J d C m Y z := by
  let u := physical A F V Y (tape (m Y + coupling R.beta • z))
  let h := (till x)
  let y := Fintype.card (Site f)
  have he (w t d i j p : ℝ) : Real.exp (-d - t + w - i + j) =
      Real.exp (w-p)* (Real.exp (p-d-t) * Real.exp (-i+j)) := by rw [← Real.exp_add,← Real.exp_add]; ring_nf
  unfold sleeves dyed exposed displaced; dsimp only
  rw [he _ _ _ _ _ (R.v*y),neg_mul]; ring!

lemma solvent_ledger (B : BudgetPoint) (Q C : Gaussian.Table (In x A F (G:=G)))
    {n : Type} [Fintype n] [DecidableEq n] (H : Gaussian.Table n) (hH : H.PosDef) (hQ : Q.PosDef) (hC : C.PosDef)
    (h : LocalRatio J) (he : 0 < R.beta) :
    spare J R.beta ^ Fintype.card (Active A x F) * Real.sqrt C.det =
      spare J R.beta ^ Fintype.card F.Free * (Real.sqrt H.det)⁻¹ *
        Real.exp (-(Fintype.card (Frozen A x F):ℝ)*Real.log (spare J R.beta) -
          (1/2)*(Real.log Q.det-Real.log H.det)+ (1/2)*Real.log (1+(Q*C-1)).det) := by
  have hp := spare_pos J h he
  have hd : (1+(Q*C-1)).det = Q.det*C.det := by rw [show (1+(Q*C-1))=Q*C by abel,Matrix.det_mul] -- which
  have hc := hC.det_pos
  have ht := hQ.det_pos
  have hz := hH.det_pos
  have hx (a : ℝ) (h : 0<a) : Real.exp ((1/2:ℝ)*Real.log a) = Real.sqrt a := by
    have he := Real.sqrt_pos.2 h
    nth_rw 1 [← Real.sq_sqrt h.le]
    rw [Real.log_pow]; norm_num; convert! Real.exp_log he using 2; ring
  let s := spare J R.beta
  let m := Fintype.card (Frozen A x F)
  have hi : Fintype.card F.Free=m+Fintype.card (Active A x F) := by
    rw [← Fintype.card_congr (Equiv.sumCompl (chill A x F)), Fintype.card_sum]
  rw [hd,Real.log_mul ht.ne' hc.ne',show -(_ : ℝ)*Real.log s - 1/2*(Real.log Q.det-Real.log H.det)+
      1/2*(Real.log Q.det+Real.log C.det) = -(Real.log (s^m)) + (1/2*Real.log H.det) + (1/2*Real.log C.det) by
        rw [Real.log_pow]; ring,
    Real.exp_add,Real.exp_add,Real.exp_neg,Real.exp_log (pow_pos hp _),hx H.det hz,hx C.det hc,hi,pow_add]
  field_simp

/-- Whole fixed-F sector scalar formula & covariance. `H` may be any
specified *positive real* reference precision (to not assume equality
of determinants across tags/trees). It factors algebraically; take the
E truncated one wherever its own certificates are produced. -/
lemma full_price (B : BudgetPoint) (hb : B.threshold=temp x)
    (C : Gaussian.Table (In x A F (G:=G))) (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    {n : Type} [Fintype n] [DecidableEq n] (H : Gaussian.Table n) (hH : H.PosDef)
    (hc : C.PosDef) (hQ : (Rows.gram T x V k W A F).PosDef)
    (h : LocalRatio J) (he : 0 < R.beta) (hl : Licenses T x V k A R W F D q J d C m) :
    let Q := Rows.gram T x V k W A F
    let M := piHaar G (Frozen A x F); let Z := cloud C
    let p := D.portion A F V (fun k a => exposed R (till x) (F.drape a) * enters T R.beta x k V (F.drape a)) k
    let v := sleeves T x V k A R W F D q J d B C m
    let s := spare J R.beta
    let ledger := Real.exp (R.v * Fintype.card (Site f))*prefactor S G R.beta*s ^ Fintype.card F.Free*(Real.sqrt H.det)⁻¹
    let cost := Real.exp (-(Fintype.card (Frozen A x F):ℝ)*Real.log s - (1/2)*(Real.log Q.det - Real.log H.det)+
      (1/2)*Real.log (1+(Q*C-1)).det)
    (∀ y, Integrable (v y) Z) ∧ Integrable (uncurry v) (M.prod Z) ∧
      sieve T R.beta x V * (∫ a, p a ∂F.order G) = banker T B V R.beta * ledger * cost *
        (∫ y, (∫ z, v y z ∂Z) ∂M) := by
  intro Q M Z p v s ledger cost
  let w := dyed T x V k A R W F D q J d C m
  let g := Real.exp (coarseTail T x B V R.beta-R.v*Fintype.card (Site f))
  have hx y z : v y z = g*w y z := sleeves_unfold ..
  refine ⟨fun y => ?_,?_,?_⟩
  · rw [show v y = fun z => g*w y z from funext (hx _)]
    exact (hl.sectionEach y).const_mul _
  · rw [show uncurry v=fun a => g*uncurry w a from funext fun a => hx a.1 a.2]
    exact hl.integer.const_mul _
  have hv := hl.result
  change (∫ a,p a ∂_) = _*∫ y,(∫ z,w y z ∂Z)∂M at hv
  rw [hv, convert_full T x V B R.beta hb]
  simp_rw [hx,integral_const_mul]
  let i := ∫ y,(∫ z,w y z ∂Z)∂M
  have hk : J.scale ^ Fintype.card (Active A x F)*chartCost C (coupling R.beta) =
      s ^ Fintype.card F.Free * (Real.sqrt H.det)⁻¹ * cost := by
    rw [scalars_align x A R F J,solvent_ledger x A R F J B Q C H hH hQ hc h he]
  have hd : Real.exp (R.v*Fintype.card (Site f)) * g = Real.exp (coarseTail T x B V R.beta) := by unfold g; rw [← Real.exp_add]; ring_nf
  rw [← hd]
  calc
    banker .. * _ * _ = banker T B V R.beta * Real.exp (R.v*Fintype.card (Site f)) * prefactor S G R.beta *
        (J.scale ^ Fintype.card (Active A x F)*chartCost C (coupling R.beta)) * g * i := by unfold i; ring
    _ = _ := by rw [hk]; unfold ledger; ring
end YM.Next.SectorChange
