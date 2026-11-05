import YM.UVExtension.Concert.Lyres
import YM.UVExtension.Concert.Ladle
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Yard
open Function Filter Set RG Wilson Lattice Precision Push Push.AbsoluteSums Finset
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration WilsonStartup Residual Averaging Geo
open Lamppost Concert
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {p : BudgetPoint} {P : Listing G n} {X:Support n} {D Y : Type}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] {M:Opening D Y} {σ C Λ b c : ℝ}
    (a:D→ Collection.Source G n)
    (K : PathData G)(v:Clip)
variable (hG : G.Simple) (F:Atlas (fork p G P.reg (preExponent p)) M (fun d=>trill p G P.reg (preExponent p) (a d).logRead) (fun _=>b))
    (H:∀ d,smoothP p P.reg (a d).logRead)

def terms (s:Finset D)(f:D→ℝ) : Collection.Source G n:= ⟨Concert.plaits s f (fun i=>(a i).logRead),0⟩

-- projection payout ledger. Ordered-Hessian equality at reference.
variable (s: Finset D)(w:D→ℝ)
include H
lemma collapse (i:ℕ)(j k:PlaqAxes): projection (P.reg i) ((terms a s w).logRead i) j k= ∑ d∈s,w d*projection (P.reg i) ((a d).logRead i) j k:=by
  simp_rw [projection]; split
  next hv=>
    let V:= wedge j (spike G); let K:=wedge k (spike G)
    let u:= (P.reg i).site; let Z:= (P.reg i).support
    let p₀ d:= (a d).logRead i
    have hh : logHessian ((terms a s w).logRead i) (V.field u) (K.field u)=∑ d∈s,w d* logHessian (p₀ d) (V.field u) (K.field u):=by
      unfold logHessian; dsimp only [terms,plaits]; simp_rw [Finset.sum_apply, Pi.smul_apply]
      -- unfolds iterate
      have ht d: p.Regular Z (p₀ d):= H d i
      have hC d:= germ_diff (ht d)
      rw [iteratedFDeriv_fun_sum_apply]; swap; · exact fun i _=> (hC i).const_smul (w i)
      rw [_root_.sum_apply]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [iteratedFDeriv_const_smul_apply']; swap; · exact hC i
      rfl
    exact hh
  next h=> simp
include hG H
omit H hG
lemma projects_ledger {a:Collection.Source G n}(hs:smoothP p P.reg a.logRead) (hv: (fork p G P.reg (preExponent p)).MeasureP (trill p G P.reg (preExponent p) a.logRead) b) : Projects (P.read a) p b:= by
  obtain ⟨f,h,hF⟩:= (fork_earns ..).1 hv
  exact ⟨hs, ⟨_,h,Quotes.segment P.reg (fun i=>(h i).1) hF⟩⟩
include F
lemma truth (i:D): (fork p G P.reg (preExponent p)).MeasureP (trill p G P.reg (preExponent p) (a i).logRead) b :=by
  obtain ⟨b,h,hb⟩:= (F.bounds _ (M.within i)).afloat
  exact ⟨_,fun j=> ⟨(h j).1,fun k=> by have hp:= (h j).2 k; rw [F.exacts,Complex.norm_real] at hp; exact hp⟩,hb⟩
include H hG
lemma stepL (_hv : Projects (P.read (terms a s w)) p c): delta (P.read (terms a s w))=∑ i∈s,w i*delta (P.read (a i)) := by
  let Y i:= P.read (a i)
  let Z i k:= censusAt (Y i) 0 axes01 axes01 k
  have hp i: Summable (Z i):= (projects_ledger (P:=P) (H i) (truth a F i)).seriesAt hG ..
  have hx : ∀ k,censusAt (P.read (terms a s w)) 0 axes01 axes01 k= ∑ i∈ s,w i*Z i k:= by
    intro k; unfold Z censusAt; dsimp only [Y, Listing.read]; split_ifs; exact collapse a H s w k ..; simp
  unfold Averaging.delta Averaging.total; simp_rw [hx]; rw [Summable.tsum_finsetSum]; swap; · exact fun i hi=> (hp i).mul_left _
  simp_rw [tsum_mul_left]; rfl
variable {P' : D→ Collection.Source G n}
lemma sale (hp:0≤b): Charm M (2*(p.threshold^2)⁻¹*b) (fun i=> delta (P.read (a i))) :=by
  apply Charm.mk; let P₀:=fork p G P.reg (preExponent p)
  let f(z:Y)i:= Meter.Finger.issue P₀ i (F.f z)
  let v i k:= Meter.Finger.effect P₀ k (trill p G P.reg (preExponent p) (a i).logRead)
  have ht:=p.threshold_pos
  apply Lamppost.bloom (x:=M.call) (f:=f) (src:=v) (b:=fun _=>b) M.within (fun i=> P₀.pollen F.pulse i) (fun i k=> (P₀.income k (w:=trill p G P.reg (preExponent p) (a i).logRead) (fun x y=> (F.exacts ..).symm)).symm) (fun i=> delta (P.read (a i))) _ (by positivity) (fun z hz=> ⟨hp,⟨le_refl _,hp⟩,fun i=> P₀.spare (F.bounds z hz) i⟩) hp
  intro s w n hn hx
  have hf : P₀.MeasureP (trill p G P.reg (preExponent p) (terms a s w).logRead) n:=by
    have hh:= P₀.clips_real (fun i k=>∑ j∈s,w j*trill p G P.reg (preExponent p) (a j).logRead i k) n (fun i=> by rw [Meter.combines]; exact hx i)
    apply (fork_earns P.reg _).2; exact (Concert.raises _ _ s w _ H).1 hh
  have he:= projects_ledger (a:=terms a s w) (Concert.blasts _ _ s w H) hf
  rw [← stepL a hG F H s w he]; rw [Real.norm_eq_abs,mul_comm _ n, ← div_eq_mul_inv]; exact (le_div_iff₀ (by positivity)).mpr ((mul_comm ..).trans_le (delta_bound hG he))
end YM.UVExtension.Yard
