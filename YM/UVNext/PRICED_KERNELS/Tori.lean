import YM.Next.FOUNDATIONS.SU2
import YM.Next.FREE_KERNELS.Rack
import YM.Push.PRICE_COMPILER.Authors
import YM.UVNext.PRICED_KERNELS.Echo



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# All-period output at a free-kernel Permit

The stronger physical identities  at ANY Side tested, with its fine side the exact ratio; can
be even or side 1/harmonic. Same Beds, SAME repaired V towers, SAME strip/Whole
C3 witness found at the earlier price. The harmonic freedoms of the probe/mean
etc are not redefined. In design `FlatBill.Estimates` and `V.Suffices` already
have arbitrary period estimates where needed, but cross & Roll affine
transport were evaluated by the consumer only at schedule periods. Obtain those
even on these sides on the realizing Horizon, independent of details of `preMap`
choice. This affords e.g. testing cover-coefficient identities released later
and using canonical path kernels priced before choosing a period. No nonlinear
estimates transferred to any other torus than they originally apply. In
particular don't reinterpret Plot bounds at an unadmitted period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Function Lattice RG RG.Supply Precision Craft Laurent Exterior Bloch Matrix
open Next.Free Work.F08
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge}

/-- The StepData built by the clock but with arbitrary sizes in the right
proportion. Same kernel, same prechoice parameters. Definitional equality to
the one used for all admitted schedules when sampling those p. -/
def again (a : Levels G) (m : ℕ) (c f : Side) (hf : f.val=c.val*(a.S.block m).val) : StepData c f :=
    ⟨(a.clock.op m 0).patch,a.clock.kernel,hf⟩
example (a : Levels G) (m p : ℕ) : again a m _ _ (a.S.oneStep m p).exact_size=a.clock.op m p := rfl

/-- Export `Present` crossings on any torus, all of trial/transport/star
equations. Require the same l table that was provided nonnegative. -/
theorem universal_diagonal (a : Levels G) {V : Horizon a} {l}
    (hV : Next.Free.Present a V l) {m N : ℕ} (hn : m < N)
    (hl₁ : 0 ≤ l (a.clock.J m)) (hl₂ : 0 ≤ l (a.clock.J (m+1))) (c f : Side) (h : f.val=c.val*(a.S.block m).val) :
    Towers.Diagonal (again a m c f h) (V.H N (m+1)) (V.H N m) (V.towers N m) := by
  let k := a.clock.kernel
  let P := Next.Free.destination a N m
  have hh : Next.Free.location a N m=P.land := Next.Free.loc_land a N m hn
  have he : Towers.Diagonal (again a m c f h) (V.H N (m+1)) (V.H N m) (P.duo a.clock.kernel.penalty) :=
    Next.Free.diagonal k (l (a.clock.J m)) (l (a.clock.J (m+1))) hl₁ hl₂ P (a.clock.adm _) _ _
      (hV.1 N (m+1) hn) (hh ▸ hV.1 N m hn.le) (c:=c) (f:=f) h
  obtain ⟨hs,hx⟩ := hV.2 N m hn
  constructor
  · rw [hs]; exact he.trial
  · rw [hx]; exact he.transport
  rw [hs,hx]; exact he.stays

section Formula
variable {L : Side} (T : Towers L) (X Y : Bed)
open Echo (Sound Across listens vertical kSound dSound fullSound oneSound noneSound heard heardAcross allAcross schedule_sides)

/-- `m` lifted as a same-scale family: the L^4 payment lives inside `net`
when physicalizing, cannot drop it. -/
def kraus (c : Side) := (net T.mf T.mf).acts c + (T.mn.acts c).transpose*T.mn.acts c + (T.o.acts c).transpose*T.o.acts c

lemma first_lift {A s : ℝ} {k : ℕ} (hp : 0 < s) (h : T.Deep s A k) : Sound (kraus T) := by
  let B := T.mf
  have hb : Whole B := ⟨s,_,hp,h.2.2.1⟩
  have hf := heard (show Whole T.mn from ⟨s,_,hp,h.1⟩)
  have hg := heard (show Whole T.o from ⟨s,_,hp,h.2.1⟩)
  exact ((heard (hb.flipped.prod hb)).plus (hf.transpose.multiply hf)).plus (hg.transpose.multiply hg)

lemma first_hear {s A : ℝ} {k : ℕ} (hp : 0 < s) (h : T.Deep s A k)
    (c f : Side) (H : f.val=c.val*L.val) :
    kraus T c = (listens T.mf c f H).transpose * listens T.mf c f H +
      (T.mn.acts c).transpose*T.mn.acts c + (T.o.acts c).transpose*T.o.acts c := by
  unfold kraus; have hh : Whole T.mf := ⟨s,_,hp,h.2.2.1⟩; rw [net_action (vertical L c f H) hh hh]

/-- Rewrite away the mean term *only in this equation* (complete stack,
ρ transport and noise), justified by the other two physical equations. No
claim of invertibility/use of d on harmonic, nor of determining mean in its
kernel. The remaining equation is a cross identity. -/
lemma orthogonal_iff {c f : Side} {S : StepData c f} (T : Towers S.patch.L)
    {X : Matrix (Co f Layers2) (Body 2 f) ℝ} {Z : Matrix (Co c Layers2) (Body 2 c) ℝ}
    (h₁ : (installed S.ratio T.T).transpose * d 1 f = d 1 c * mean S)
    (h₂ : Real.sqrt S.kernel.penalty • (T.mn.acts c).transpose= Z * d 1 c) :
    (installed S.ratio T.mf).transpose * (X * d 1 f) +
      (T.mn.acts c).transpose * (- Real.sqrt S.kernel.penalty • mean S)=0 ↔
      (X * d 1 f).transpose * installed S.ratio T.mf = (d 1 f).transpose * (installed S.ratio T.T * Z.transpose) := by
  simp only [Matrix.mul_smul,← Matrix.smul_mul, neg_smul, Matrix.mul_neg,h₂,Matrix.mul_assoc,
    ← h₁,← sub_eq_add_neg,sub_eq_zero]
  rw [show (X*d 1 f).transpose * installed S.ratio T.mf=((installed S.ratio T.mf).transpose * (X*d 1 f))ᵀ from (by simp only [transpose_mul,transpose_transpose]),
    show (d 1 f).transpose * (installed S.ratio T.T * Z.transpose)=(Z*((installed S.ratio T.T).transpose * d 1 f))ᵀ from (by simp only [transpose_mul,transpose_mul,transpose_transpose,Matrix.mul_assoc])]
  exact ⟨fun he => congr_arg Matrix.transpose he, fun he => Matrix.transpose_injective he⟩

end Formula

section Check
open Echo (Sound Across listens vertical kSound dSound fullSound oneSound noneSound heard heardAcross allAcross schedule_sides)

/-- `V` chosen by any preMap use. Its rows themselves now confer all-period
Stack. Applies to any horizon where the mean/Diagonal transport is
periodically verified and Suffices on all clock tests. The latter is not assumed
for these inputs later: obtained for free at exactly P.frozen by `Wired`. -/
theorem complete_roll {a : Levels G} {V : Horizon a} {K : MapPrices} (hv : V.Suffices K)
    {N m : ℕ} (hm : m < N) (c f : Side) (hf : f.val=c.val*(a.S.block m).val) :
    let S := again a m c f hf
    Towers.Diagonal S (V.H N (m+1)) (V.H N m) (V.towers N m) →
      Towers.Roll S (V.H N (m+1)) (V.H N m) (V.towers N m) (a.params (m+1)).clip (a.params m).clip := by
  let L := a.S.block m
  let i := a.clock.J m; let j := a.clock.J (m+1)
  let hi (x) := K.alpha_pos x
  have hh := hv.costs N m hm
  let U := V.towers N m
  let X := V.H N (m+1); let Y := V.H N m
  let x := (a.params (m+1)).clip; let y := (a.params m).clip
  have ha : X.covered (K.α j) (K.Ω j) := hv.rows N (m+1) hm
  have hg : Y.covered (K.α i) (K.Ω i) := hv.rows N m hm.le
  have hX := fullSound (M:=X) ⟨_,_,hi j,ha.2.2.2.1⟩ x
  have hY := fullSound (M:=Y) ⟨_,_,hi i,hg.2.2.2.1⟩ y
  have hZ := heard (show Whole Y.metric from ⟨_,_,hi _,hg.2.1⟩)
  let cS p := a.S.side m p; let fS p := a.S.side (m+1) p
  have hS p : (fS p).val=(cS p).val*L.val := (a.S.oneStep m p).exact_size
  have hC := schedule_sides a.S m
  let r := Real.sqrt a.clock.kernel.penalty
  have hn : Whole U.mn := ⟨_,_,hi _,hh.1⟩
  have hU : Whole U.mf := ⟨_,_,hi _,hh.2.2.1⟩
  obtain ⟨hQ,hT⟩ := hh.2.2.2 [] (Nat.zero_le _)
  have hA0 := heardAcross (L:=L) (show Whole U.A0 from ⟨_,_,hi _,hQ⟩)
  have hT0 := heardAcross (L:=L) (show Whole U.T from ⟨_,_,hi _,hT⟩)
  have hF := heardAcross (L:=L) hU
  have het n : r • (U.mn.acts n).transpose = Y.full y n*d 1 n := Echo.all
    ((heard hn).transpose.scales r) (hY.multiply (dSound 1)) cS hC (fun p => (hv.stack N m p hm).n) n
  intro S hS'
  refine ⟨?_,het c,?_,?_,?_,(orthogonal_iff (S:=S) (X:=X.full x f) (Z:=Y.full y c) U hS'.transport (het c)).mpr ?_⟩
  · change (listens U.mf c f hf).transpose * listens U.mf c f hf +
        (U.mn.acts c).transpose*U.mn.acts c + (U.o.acts c).transpose*U.o.acts c = 1
    rw [← show kraus U c = _ from first_hear U (hi _) hh c f hf]
    exact Echo.all (first_lift U (hi _) hh) (oneSound Layers2) cS hC (fun p =>
      (first_hear U (hi _) hh (cS p) (fS p) (hS p)).trans (hv.stack N m p hm).m) c
  · have hh (p : ℕ) : listens U.mf (cS p) (fS p) (hS p)*(Y.full y (cS p) * d 1 (cS p)) =
        (X.full x (fS p)*d 1 (fS p))*listens U.A0 (cS p) (fS p) (hS p) := by rw [← Matrix.mul_assoc]; exact (hv.stack N m p hm).fPart
    have hr := allAcross (L:=L) (hF.then (hY.multiply (dSound 1))) (hA0.from (hX.multiply (dSound 1))) cS fS hS hC hh c f hf
    change listens U.mf c f hf * Y.full y c * d 1 c = X.full x f * d 1 f * listens U.A0 c f hf
    rw [Matrix.mul_assoc (listens U.mf c f hf)]; exact hr
  · exact Echo.all (((heard hn).multiply hY).multiply (dSound 1)) ((kSound hZ).scales r⁻¹)
      cS hC (fun p => (hv.stack N m p hm).nPart) c
  · exact Echo.all (((heard (show Whole U.o from ⟨_,_,hi _,hh.2.1⟩)).multiply hY).multiply (dSound 1))
      (noneSound _ _) cS hC (fun p => (hv.stack N m p hm).oPart) c
  have ht (p : ℕ) := (orthogonal_iff (S:=a.clock.op m p) (X:=X.full x (fS p)) (Z:=Y.full y (cS p)) U
    (hv.crossings N m p hm).transport (hv.stack N m p hm).n).mp (hv.stack N m p hm).orthogonal
  exact allAcross (L:=L) (hF.from ((hX.multiply (dSound 1)).transpose))
    ((hT0.then hY.transpose).from (dSound 1).transpose) cS fS hS hC ht c f hf

end Check

section Conclusion
open Echo (Sound Across listens vertical kSound dSound fullSound oneSound noneSound heard heardAcross allAcross schedule_sides)




end Conclusion
end YM.UVNext.PricedKernels
